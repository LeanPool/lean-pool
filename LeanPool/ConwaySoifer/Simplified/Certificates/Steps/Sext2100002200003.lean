/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext210000220000
import Mathlib.Tactic.FinCases

/-!
# Sext 210000 220000 3

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
namespace Sext210000220000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner5Part0 : FanWitness := (.next ([5250000000000], [348000000000]) (some (4, 1, 5)) (some
    (4, 1, 5)) (.next ([8055000000000, 9000000000000], [1110000000000, -9000000000000]) (some (4, 1,
    5)) (some (4, 1, 5)) (.next ([6165000000000], [3000000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([348000000000], [267000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([2520000000000], [5115000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2172000000000],
    [4848000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([750000000000], [1770000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([915000000000], [2652000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([1890000000000, 9000000000000], [5865000000000, 0]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([1542000000000, 9000000000000], [5598000000000, 0]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([300000000000], [3000000000000]) (some (4, 1, 5)) (some (0, 1, 5))
    (.next ([0, 0], [1890000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-480000000000], [8415000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-348000000000],
    [5598000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1110000000000, 9000000000000],
    [9165000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3000000000000], [9165000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-267000000000], [615000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-5115000000000], [7635000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-4848000000000], [7020000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1770000000000], [2520000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2652000000000],
    [3567000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5865000000000, 0], [7755000000000,
    9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5598000000000, 0], [7140000000000,
    9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3000000000000], [3300000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 5, 5)) (some (0, 5,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan26Owner0Part0 : FanWitness := (.next ([-1005000000000], [3750000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([-1260000000000], [4005000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    (.next ([-1635000000000], [5010000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([-1635000000000], [4755000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-375000000000],
    [1005000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-2835000000000], [7080000000000])
    (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-4545000000000], [9915000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([-375000000000], [750000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    (.next ([-5085000000000], [10125000000000]) (some (9, 3, 5)) (some (9, 3, 6)) (.next
    ([-2955000000000], [5505000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([-1710000000000],
    [2835000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([-330000000000], [540000000000])
    (some (9, 3, 6)) (some (9, 3, 6)) (.next ([-630000000000], [1005000000000]) (some (9, 3, 6))
    (some (9, 4, 6)) (.next ([-3705000000000], [5880000000000]) (some (9, 4, 6)) (some (9, 4, 6))
    (.next ([-3960000000000], [5880000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([-2250000000000], [3045000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-4335000000000],
    [5505000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-4335000000000], [5250000000000])
    (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-1380000000000], [1635000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) (.next ([-5790000000000], [6630000000000]) (some (9, 4, 6)) (some (9, 4, 6))
    (.next ([-3960000000000], [4500000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([-6540000000000], [7005000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-6000000000000],
    [6300000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-6795000000000], [7005000000000])
    (some (9, 4, 6)) (some (9, 4, 6)) (.terminal (some (9, 4, 6)) (some (9, 4, 6)) (some (9, 4,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan26Owner0Part1 : FanWitness := (.next ([375000000000], [630000000000]) (some (9, 3, 4)) (some
    (9, 3, 4)) (.next ([2175000000000], [3705000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next
    ([1920000000000], [3960000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([795000000000],
    [2250000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([1170000000000], [4335000000000])
    (some (9, 3, 4)) (some (9, 3, 4)) (.next ([915000000000], [4335000000000]) (some (9, 3, 4))
    (some (9, 3, 4)) (.next ([255000000000], [1380000000000]) (some (9, 3, 4)) (some (9, 3, 4))
    (.next ([840000000000], [5790000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next
    ([540000000000], [3960000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([465000000000],
    [6540000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([300000000000], [6000000000000])
    (some (9, 3, 4)) (some (9, 3, 4)) (.next ([210000000000], [6795000000000]) (some (9, 3, 4))
    (some (9, 3, 5)) (.next ([0], [255000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([-75000000000], [6750000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-330000000000],
    [7005000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-540000000000], [7170000000000])
    (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-255000000000], [3375000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([-795000000000], [7170000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    (.next ([-1080000000000], [7380000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([-255000000000], [1635000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-1170000000000],
    [6795000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-1335000000000], [7380000000000])
    (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-1260000000000], [5385000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([-1710000000000], [7005000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    fan26Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner0Part0 : FanWitness := (.next ([-375000000000], [1485000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([-630000000000], [1740000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    (.next ([-375000000000], [1005000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([-1005000000000], [2490000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-375000000000],
    [750000000000]) (some (9, 3, 5)) (some (9, 3, 9)) (.next ([-2955000000000], [5505000000000])
    (some (9, 3, 9)) (some (9, 3, 9)) (.next ([-1485000000000], [2490000000000]) (some (9, 3, 9))
    (some (9, 3, 9)) (.next ([-1710000000000], [2835000000000]) (some (1, 3, 9)) (some (1, 3, 9))
    (.next ([-330000000000], [540000000000]) (some (1, 3, 9)) (some (1, 3, 9)) (.next
    ([-630000000000], [1005000000000]) (some (1, 3, 9)) (some (1, 4, 9)) (.next ([-3705000000000],
    [5880000000000]) (some (1, 4, 9)) (some (1, 4, 9)) (.next ([-1110000000000], [1740000000000])
    (some (1, 4, 9)) (some (1, 4, 9)) (.next ([-3960000000000], [5880000000000]) (some (1, 4, 9))
    (some (1, 4, 9)) (.next ([-2250000000000], [3045000000000]) (some (1, 4, 9)) (some (1, 4, 9))
    (.next ([-1110000000000], [1485000000000]) (some (1, 4, 9)) (some (1, 4, 9)) (.next
    ([-5445000000000], [6990000000000]) (some (1, 4, 9)) (some (1, 4, 9)) (.next ([-4335000000000],
    [5505000000000]) (some (1, 4, 9)) (some (1, 4, 9)) (.next ([-4335000000000], [5250000000000])
    (some (1, 4, 9)) (some (1, 4, 9)) (.next ([-1380000000000], [1635000000000]) (some (1, 4, 9))
    (some (1, 4, 9)) (.next ([-5790000000000], [6630000000000]) (some (1, 4, 9)) (some (1, 4, 9))
    (.next ([-3960000000000], [4500000000000]) (some (1, 4, 9)) (some (1, 4, 9)) (.next
    ([-6540000000000], [7005000000000]) (some (1, 4, 9)) (some (2, 4, 9)) (.next ([-6000000000000],
    [6300000000000]) (some (2, 4, 9)) (some (2, 4, 9)) (.next ([-6795000000000], [7005000000000])
    (some (2, 4, 9)) (some (2, 4, 9)) (.terminal (some (2, 4, 9)) (some (2, 4, 9)) (some (2, 4,
    9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner0Part1 : FanWitness := (.next ([1920000000000], [3960000000000]) (some (9, 3, 4))
    (some (9, 3, 4)) (.next ([795000000000], [2250000000000]) (some (9, 3, 4)) (some (9, 3, 4))
    (.next ([375000000000], [1110000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next
    ([1545000000000], [5445000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([1170000000000],
    [4335000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([915000000000], [4335000000000])
    (some (9, 3, 4)) (some (9, 3, 4)) (.next ([255000000000], [1380000000000]) (some (9, 3, 4))
    (some (9, 3, 4)) (.next ([840000000000], [5790000000000]) (some (9, 3, 4)) (some (9, 3, 4))
    (.next ([540000000000], [3960000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next
    ([465000000000], [6540000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([300000000000],
    [6000000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([210000000000], [6795000000000])
    (some (9, 3, 4)) (some (9, 3, 5)) (.next ([0], [255000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    (.next ([-75000000000], [6750000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([-165000000000], [8280000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-330000000000],
    [7005000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-540000000000], [7170000000000])
    (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-705000000000], [8490000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([-795000000000], [7170000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    (.next ([-1080000000000], [7380000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([-255000000000], [1635000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-1170000000000],
    [6795000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-1335000000000], [7380000000000])
    (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-1710000000000], [7005000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) fan27Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner4Part0 : FanWitness := (.next ([2010000000000], [2265000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([2040000000000, 9000000000000], [2835000000000, -9000000000000]) (some
    (4, 1, 5)) (some (4, 1, 5)) (.next ([1635000000000], [2745000000000]) (some (4, 1, 5)) (some (4,
    1, 5)) (.next ([1890000000000, 9000000000000], [4545000000000]) (some (4, 1, 5)) (some (4, 1,
    5)) (.next ([2340000000000], [6660000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([105000000000], [375000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([705000000000],
    [3915000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([630000000000], [4620000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([330000000000], [4395000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([150000000000], [4725000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([0], [4545000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([-225000000000,
    9000000000000], [7110000000000, -9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-2115000000000], [9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2730000000000,
    9000000000000], [5250000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2265000000000],
    [4275000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2835000000000, 9000000000000],
    [4875000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2745000000000], [4380000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4545000000000], [6435000000000, 9000000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-6660000000000], [9000000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-375000000000], [480000000000]) (some (0, 1, 5)) (some (0, 5, 5))
    (.next ([-3915000000000], [4620000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next
    ([-4620000000000], [5250000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-4395000000000],
    [4725000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-4725000000000], [4875000000000])
    (some (0, 5, 5)) (some (0, 5, 5)) (.terminal (some (0, 5, 5)) (some (0, 5, 5)) (some (0, 5,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan29Owner0Part0 : FanWitness := (.next ([-1710000000000], [7005000000000]) (some (0, 3, 9))
    (some (0, 3, 9)) (.next ([-1830000000000], [7380000000000]) (some (0, 3, 9)) (some (0, 3, 9))
    (.next ([-2205000000000], [8385000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next
    ([-2460000000000], [8640000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-2205000000000],
    [7005000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-3210000000000], [9015000000000])
    (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-375000000000], [1005000000000]) (some (0, 3, 9))
    (some (0, 3, 9)) (.next ([-375000000000], [750000000000]) (some (0, 3, 9)) (some (0, 3, 9))
    (.next ([-2955000000000], [5505000000000]) (some (0, 3, 9)) (some (1, 3, 9)) (.next
    ([-1710000000000], [2835000000000]) (some (1, 3, 9)) (some (1, 3, 9)) (.next ([-330000000000],
    [540000000000]) (some (1, 3, 9)) (some (1, 3, 9)) (.next ([-630000000000], [1005000000000])
    (some (1, 3, 9)) (some (1, 4, 9)) (.next ([-3705000000000], [5880000000000]) (some (1, 4, 9))
    (some (1, 4, 9)) (.next ([-3960000000000], [5880000000000]) (some (1, 4, 9)) (some (1, 4, 9))
    (.next ([-2250000000000], [3045000000000]) (some (1, 4, 9)) (some (1, 4, 9)) (.next
    ([-4335000000000], [5505000000000]) (some (1, 4, 9)) (some (1, 4, 9)) (.next ([-7710000000000],
    [9555000000000]) (some (1, 4, 9)) (some (1, 4, 9)) (.next ([-4335000000000], [5250000000000])
    (some (1, 4, 9)) (some (1, 4, 9)) (.next ([-1380000000000], [1635000000000]) (some (1, 4, 9))
    (some (1, 4, 9)) (.next ([-5790000000000], [6630000000000]) (some (1, 4, 9)) (some (1, 4, 9))
    (.next ([-3960000000000], [4500000000000]) (some (1, 4, 9)) (some (1, 4, 9)) (.next
    ([-6540000000000], [7005000000000]) (some (1, 4, 9)) (some (2, 4, 9)) (.next ([-6000000000000],
    [6300000000000]) (some (2, 4, 9)) (some (2, 4, 9)) (.next ([-6795000000000], [7005000000000])
    (some (2, 4, 9)) (some (2, 4, 9)) (.terminal (some (2, 4, 9)) (some (2, 4, 9)) (some (2, 4,
    9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan29Owner0Part1 : FanWitness := (.next ([2175000000000], [3705000000000]) (some (8, 3, 9))
    (some (8, 3, 9)) (.next ([1920000000000], [3960000000000]) (some (8, 3, 9)) (some (8, 3, 9))
    (.next ([795000000000], [2250000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next
    ([1170000000000], [4335000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([1845000000000],
    [7710000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([915000000000], [4335000000000])
    (some (8, 3, 9)) (some (8, 3, 9)) (.next ([255000000000], [1380000000000]) (some (8, 3, 9))
    (some (8, 3, 9)) (.next ([840000000000], [5790000000000]) (some (8, 3, 9)) (some (8, 3, 9))
    (.next ([540000000000], [3960000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next
    ([465000000000], [6540000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([300000000000],
    [6000000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([210000000000], [6795000000000])
    (some (8, 3, 9)) (some (8, 3, 9)) (.next ([0], [255000000000]) (some (8, 3, 9)) (some (8, 3, 9))
    (.next ([-75000000000], [6750000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next
    ([-330000000000], [7005000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-540000000000],
    [7170000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-795000000000], [7170000000000])
    (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-990000000000], [8835000000000]) (some (0, 3, 9))
    (some (0, 3, 9)) (.next ([-1200000000000], [8505000000000]) (some (0, 3, 9)) (some (0, 3, 9))
    (.next ([-1080000000000], [7380000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next
    ([-255000000000], [1635000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-1170000000000],
    [6795000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-1335000000000], [7380000000000])
    (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-1830000000000], [7635000000000]) (some (0, 3, 9))
    (some (0, 3, 9)) fan29Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan30Owner0Part0 : FanWitness := (.next ([-900000000000], [5745000000000]) (some (0, 3, 9))
    (some (0, 3, 9)) (.next ([-1155000000000], [7200000000000]) (some (0, 3, 9)) (some (0, 3, 9))
    (.next ([-1170000000000], [6795000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next
    ([-1335000000000], [7380000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-1710000000000],
    [7005000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-1905000000000], [7755000000000])
    (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-375000000000], [1005000000000]) (some (0, 3, 9))
    (some (0, 3, 9)) (.next ([-375000000000], [750000000000]) (some (0, 3, 9)) (some (0, 3, 9))
    (.next ([-2955000000000], [5505000000000]) (some (0, 3, 9)) (some (1, 3, 9)) (.next
    ([-1710000000000], [2835000000000]) (some (1, 3, 9)) (some (1, 3, 9)) (.next ([-330000000000],
    [540000000000]) (some (1, 3, 9)) (some (1, 3, 9)) (.next ([-630000000000], [1005000000000])
    (some (1, 3, 9)) (some (1, 4, 9)) (.next ([-3705000000000], [5880000000000]) (some (1, 4, 9))
    (some (1, 4, 9)) (.next ([-3960000000000], [5880000000000]) (some (1, 4, 9)) (some (1, 4, 9))
    (.next ([-2250000000000], [3045000000000]) (some (1, 4, 9)) (some (1, 4, 9)) (.next
    ([-6405000000000], [8295000000000]) (some (1, 4, 9)) (some (1, 4, 9)) (.next ([-4335000000000],
    [5505000000000]) (some (1, 4, 9)) (some (1, 4, 9)) (.next ([-4335000000000], [5250000000000])
    (some (1, 4, 9)) (some (1, 4, 9)) (.next ([-1380000000000], [1635000000000]) (some (1, 4, 9))
    (some (1, 4, 9)) (.next ([-5790000000000], [6630000000000]) (some (1, 4, 9)) (some (1, 4, 9))
    (.next ([-3960000000000], [4500000000000]) (some (1, 4, 9)) (some (1, 4, 9)) (.next
    ([-6540000000000], [7005000000000]) (some (1, 4, 9)) (some (2, 4, 9)) (.next ([-6000000000000],
    [6300000000000]) (some (2, 4, 9)) (some (2, 4, 9)) (.next ([-6795000000000], [7005000000000])
    (some (2, 4, 9)) (some (2, 4, 9)) (.terminal (some (2, 4, 9)) (some (2, 4, 9)) (some (2, 4,
    9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan30Owner0Part1 : FanWitness := (.next ([2175000000000], [3705000000000]) (some (8, 3, 9))
    (some (8, 3, 9)) (.next ([1920000000000], [3960000000000]) (some (8, 3, 9)) (some (8, 3, 9))
    (.next ([795000000000], [2250000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next
    ([1890000000000], [6405000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([1170000000000],
    [4335000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([915000000000], [4335000000000])
    (some (8, 3, 9)) (some (8, 3, 9)) (.next ([255000000000], [1380000000000]) (some (8, 3, 9))
    (some (8, 3, 9)) (.next ([840000000000], [5790000000000]) (some (8, 3, 9)) (some (8, 3, 9))
    (.next ([540000000000], [3960000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next
    ([465000000000], [6540000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([300000000000],
    [6000000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([210000000000], [6795000000000])
    (some (8, 3, 9)) (some (8, 3, 9)) (.next ([0], [255000000000]) (some (8, 3, 9)) (some (8, 3, 9))
    (.next ([-75000000000], [6750000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next
    ([-330000000000], [7005000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-540000000000],
    [7170000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-525000000000], [6375000000000])
    (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-525000000000], [6120000000000]) (some (0, 3, 9))
    (some (0, 3, 9)) (.next ([-795000000000], [7170000000000]) (some (0, 3, 9)) (some (0, 3, 9))
    (.next ([-945000000000], [7530000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next
    ([-900000000000], [7125000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-1080000000000],
    [7380000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-255000000000], [1635000000000])
    (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-1155000000000], [7380000000000]) (some (0, 3, 9))
    (some (0, 3, 9)) fan30Owner0Part0))))))))))))))))))))))))

theorem excluded24_1 : ExcludedOn (model24.B 1 ++ [step24.q]) 9000000000000 (model24.caps 1)
    (model24.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1890000000000, 9000000000000], [1890000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([2835000000000], [4110000000000,
      -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([2835000000000], [6000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([945000000000, -9000000000000], [7890000000000,
      9000000000000]) (some (0, 3, 2)) none (.next ([0, 0], [1890000000000, 9000000000000]) none
      none (.next ([-1890000000000, -9000000000000], [3780000000000, 18000000000000]) none none
      (.next ([-4110000000000, 9000000000000], [6945000000000, -9000000000000]) (some (3, 3, 0))
      (some (3, 3, 0)) (.next ([-6000000000000], [8835000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-7890000000000, -9000000000000], [8835000000000, 0]) (some (3, 1, 0)) (some (3, 1,
      0)) (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_2 : ExcludedOn (model24.B 2 ++ [step24.q]) 9000000000000 (model24.caps 2)
    (model24.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_3 : ExcludedOn (model24.B 3 ++ [step24.q]) 9000000000000 (model24.caps 3)
    (model24.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_4 : ExcludedOn (model24.B 4 ++ [step24.q]) 9000000000000 (model24.caps 4)
    (model24.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_5 : ExcludedOn (model24.B 5 ++ [step24.q]) 9000000000000 (model24.caps 5)
    (model24.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7935000000000], [480000000000]) (some (5, 0, 5))
      (some (5, 1, 5)) fan24Owner5Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_6 : ExcludedOn (model24.B 6 ++ [step24.q]) 9000000000000 (model24.caps 6)
    (model24.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2055000000000, 9000000000000], [945000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([2835000000000], [4110000000000,
      -9000000000000]) (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1890000000000, 9000000000000],
      [7110000000000, -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([165000000000],
      [2835000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1890000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-945000000000, 9000000000000],
      [3000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-4110000000000, 9000000000000],
      [6945000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-7110000000000,
      9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2835000000000], [3000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 2 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_1 : ExcludedOn (model25.B 1 ++ [step25.q]) 9000000000000 (model25.caps 1)
    (model25.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_2 : ExcludedOn (model25.B 2 ++ [step25.q]) 9000000000000 (model25.caps 2)
    (model25.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_4 : ExcludedOn (model25.B 4 ++ [step25.q]) 9000000000000 (model25.caps 4)
    (model25.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4575000000000], [555000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([4095000000000], [780000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([2520000000000, 9000000000000], [2610000000000, -9000000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([225000000000], [255000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([3945000000000], [4545000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next
      ([2040000000000, 9000000000000], [2835000000000, -9000000000000]) (some (5, 1, 3)) (some (5,
      1, 3)) (.next ([1890000000000, 9000000000000], [4545000000000]) (some (5, 1, 3)) (some (5, 1,
      3)) (.next ([585000000000], [3915000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([630000000000], [4500000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([330000000000],
      [4395000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([150000000000], [4725000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([0], [4545000000000]) (some (5, 1, 3)) (some (5, 1,
      3)) (.next ([-555000000000], [5130000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-780000000000], [4875000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2610000000000,
      9000000000000], [5130000000000]) (some (0, 1, 3)) (some (0, 1, 5)) (.next ([-255000000000],
      [480000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4545000000000], [8490000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2835000000000, 9000000000000], [4875000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4545000000000], [6435000000000, 9000000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3915000000000], [4500000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([-4500000000000], [5130000000000]) (some (0, 1, 5)) (some (0, 2, 5))
      (.next ([-4395000000000], [4725000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-4725000000000], [4875000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2,
      5)) (some (0, 2, 5)) (some (0, 2, 5))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_5 : ExcludedOn (model25.B 5 ++ [step25.q]) 9000000000000 (model25.caps 5)
    (model25.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_6 : ExcludedOn (model25.B 6 ++ [step25.q]) 9000000000000 (model25.caps 6)
    (model25.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_7 : ExcludedOn (model25.B 7 ++ [step25.q]) 9000000000000 (model25.caps 7)
    (model25.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_8 : ExcludedOn (model25.B 8 ++ [step25.q]) 9000000000000 (model25.caps 8)
    (model25.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4080000000000], [945000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([5055000000000], [3945000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([135000000000], [4920000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([30000000000], [3945000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [5025000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.next ([-945000000000], [5025000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-3945000000000], [9000000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-4920000000000], [5055000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-3945000000000], [3975000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded25_4
    · exact excluded25_5
    · exact excluded25_6
    · exact excluded25_7
    · exact excluded25_8
    · exact excluded25_9
theorem next25 : model25.insert step25 = model26 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded26_0 : ExcludedOn (model26.B 0 ++ [step26.q]) 9000000000000 (model26.caps 0)
    (model26.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6675000000000], [75000000000]) (some (6, 9, 4))
      (some (7, 9, 4)) (.next ([6675000000000], [330000000000]) (some (7, 9, 4)) (some (7, 9, 4))
      (.next ([6630000000000], [540000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next
      ([3120000000000], [255000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next ([6375000000000],
      [795000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next ([6300000000000], [1080000000000])
      (some (7, 9, 4)) (some (7, 9, 4)) (.next ([1380000000000], [255000000000]) (some (7, 9, 4))
      (some (7, 9, 4)) (.next ([5625000000000], [1170000000000]) (some (7, 9, 4)) (some (7, 9, 4))
      (.next ([6045000000000], [1335000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next
      ([4125000000000], [1260000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next ([5295000000000],
      [1710000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next ([2745000000000], [1005000000000])
      (some (7, 9, 4)) (some (7, 9, 4)) (.next ([2745000000000], [1260000000000]) (some (7, 9, 4))
      (some (7, 9, 4)) (.next ([3375000000000], [1635000000000]) (some (7, 9, 4)) (some (7, 9, 4))
      (.next ([3120000000000], [1635000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next
      ([630000000000], [375000000000]) (some (7, 9, 4)) (some (9, 9, 4)) (.next ([4245000000000],
      [2835000000000]) (some (9, 9, 4)) (some (9, 9, 4)) (.next ([5370000000000], [4545000000000])
      (some (9, 2, 4)) (some (9, 2, 4)) (.next ([375000000000], [375000000000]) (some (9, 2, 4))
      (some (9, 2, 4)) (.next ([5040000000000], [5085000000000]) (some (9, 2, 4)) (some (9, 2, 4))
      (.next ([2550000000000], [2955000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next
      ([1125000000000], [1710000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next ([210000000000],
      [330000000000]) (some (9, 2, 4)) (some (9, 3, 4)) fan26Owner0Part1))))))))))))))))))))))))
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded26_1 : ExcludedOn (model26.B 1 ++ [step26.q]) 9000000000000 (model26.caps 1)
    (model26.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_2 : ExcludedOn (model26.B 2 ++ [step26.q]) 9000000000000 (model26.caps 2)
    (model26.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_3 : ExcludedOn (model26.B 3 ++ [step26.q]) 9000000000000 (model26.caps 3)
    (model26.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4275000000000], [30000000000]) (some (2, 0, 4))
      (some (3, 0, 4)) (.next ([4575000000000], [675000000000]) (some (3, 0, 4)) (some (3, 0, 4))
      (.next ([3630000000000], [975000000000]) (some (3, 0, 4)) (some (3, 4, 4)) (.next
      ([6270000000000, 9000000000000], [3360000000000, -9000000000000]) (some (3, 4, 1)) (some (3,
      4, 1)) (.next ([2640000000000, 9000000000000], [2385000000000, -9000000000000]) (some (3, 4,
      1)) (some (3, 4, 1)) (.next ([4380000000000], [5250000000000]) (some (3, 4, 1)) (some (3, 4,
      2)) (.next ([1890000000000, 9000000000000], [5055000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([750000000000], [4275000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0],
      [5055000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-30000000000], [4305000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-675000000000], [5250000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-975000000000], [4605000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([-3360000000000, 9000000000000], [9630000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([-2385000000000, 9000000000000], [5025000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([-5250000000000], [9630000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-5055000000000, 0], [6945000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-4275000000000], [5025000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.terminal (some (0, 4,
      2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded26_5 : ExcludedOn (model26.B 5 ++ [step26.q]) 9000000000000 (model26.caps 5)
    (model26.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_6 : ExcludedOn (model26.B 6 ++ [step26.q]) 9000000000000 (model26.caps 6)
    (model26.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6675000000000], [75000000000]) (some (9, 2, 4))
      (some (9, 2, 4)) (.next ([8115000000000], [165000000000]) (some (9, 2, 4)) (some (9, 2, 4))
      (.next ([6675000000000], [330000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next
      ([6630000000000], [540000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next ([7785000000000],
      [705000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next ([6375000000000], [795000000000])
      (some (9, 2, 4)) (some (9, 2, 4)) (.next ([6300000000000], [1080000000000]) (some (9, 2, 4))
      (some (9, 2, 4)) (.next ([1380000000000], [255000000000]) (some (9, 2, 4)) (some (9, 2, 4))
      (.next ([5625000000000], [1170000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next
      ([6045000000000], [1335000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next ([5295000000000],
      [1710000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next ([1110000000000], [375000000000])
      (some (9, 2, 4)) (some (9, 2, 4)) (.next ([1110000000000], [630000000000]) (some (9, 2, 4))
      (some (9, 2, 4)) (.next ([630000000000], [375000000000]) (some (9, 2, 4)) (some (9, 2, 4))
      (.next ([1485000000000], [1005000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next
      ([375000000000], [375000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next ([2550000000000],
      [2955000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next ([1005000000000], [1485000000000])
      (some (9, 2, 4)) (some (9, 2, 4)) (.next ([1125000000000], [1710000000000]) (some (9, 2, 4))
      (some (9, 2, 4)) (.next ([210000000000], [330000000000]) (some (9, 2, 4)) (some (9, 3, 4))
      (.next ([375000000000], [630000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next
      ([2175000000000], [3705000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([630000000000],
      [1110000000000]) (some (9, 3, 4)) (some (9, 3, 4)) fan27Owner0Part1))))))))))))))))))))))))
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_1 : ExcludedOn (model27.B 1 ++ [step27.q]) 9000000000000 (model27.caps 1)
    (model27.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_2 : ExcludedOn (model27.B 2 ++ [step27.q]) 9000000000000 (model27.caps 2)
    (model27.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3330000000000], [75000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([4845000000000], [2040000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([2640000000000, 9000000000000], [1440000000000, -9000000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([4005000000000, 9000000000000], [4995000000000, -9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([1890000000000, 9000000000000], [4155000000000, 0])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([1365000000000], [3555000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([2115000000000], [6885000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([750000000000], [3330000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0],
      [4155000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-75000000000], [3405000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-2040000000000], [6885000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-1440000000000, 9000000000000], [4080000000000, 0]) (some (0, 4, 3))
      (some (4, 4, 3)) (.next ([-4995000000000, 9000000000000], [9000000000000, 0]) (some (4, 4, 3))
      (some (4, 4, 3)) (.next ([-4155000000000, 0], [6045000000000, 9000000000000]) (some (4, 2, 3))
      (some (4, 2, 3)) (.next ([-3555000000000], [4920000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([-6885000000000], [9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-3330000000000], [4080000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some (4, 2,
      3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_4 : ExcludedOn (model27.B 4 ++ [step27.q]) 9000000000000 (model27.caps 4)
    (model27.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6885000000000], [225000000000, -9000000000000])
      (some (5, 0, 5)) (some (5, 1, 5)) (.next ([6885000000000], [2115000000000]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([2520000000000, 9000000000000], [2730000000000, -9000000000000])
      (some (4, 1, 5)) (some (4, 1, 5)) fan27Owner4Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_5 : ExcludedOn (model27.B 5 ++ [step27.q]) 9000000000000 (model27.caps 5)
    (model27.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_6 : ExcludedOn (model27.B 6 ++ [step27.q]) 9000000000000 (model27.caps 6)
    (model27.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_7 : ExcludedOn (model27.B 7 ++ [step27.q]) 9000000000000 (model27.caps 7)
    (model27.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_8 : ExcludedOn (model27.B 8 ++ [step27.q]) 9000000000000 (model27.caps 8)
    (model27.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_1 : ExcludedOn (model28.B 1 ++ [step28.q]) 9000000000000 (model28.caps 1)
    (model28.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_2 : ExcludedOn (model28.B 2 ++ [step28.q]) 9000000000000 (model28.caps 2)
    (model28.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3330000000000], [75000000000]) (some (0, 0, 4))
      (some (0, 0, 4)) (.next ([2640000000000, 9000000000000], [1440000000000, -9000000000000])
      (some (0, 0, 4)) (some (0, 1, 4)) (.next ([5625000000000], [3180000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([2985000000000, -9000000000000], [1740000000000, 9000000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([1890000000000, 9000000000000], [4155000000000, 0])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([750000000000], [3330000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([150000000000], [4725000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([150000000000], [8880000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [4155000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-75000000000], [3405000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-1440000000000, 9000000000000], [4080000000000, 0])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-3180000000000], [8805000000000]) (some (0, 1, 4))
      (some (0, 2, 4)) (.next ([-1740000000000, -9000000000000], [4725000000000, 0]) (some (0, 2,
      4)) (some (0, 2, 4)) (.next ([-4155000000000, 0], [6045000000000, 9000000000000]) (some (0, 2,
      4)) (some (0, 4, 4)) (.next ([-3330000000000], [4080000000000]) (some (0, 4, 4)) (some (0, 4,
      4)) (.next ([-4725000000000], [4875000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.next
      ([-8880000000000], [9030000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4,
      3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded28_3 : ExcludedOn (model28.B 3 ++ [step28.q]) 9000000000000 (model28.caps 3)
    (model28.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_4 : ExcludedOn (model28.B 4 ++ [step28.q]) 9000000000000 (model28.caps 4)
    (model28.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_5 : ExcludedOn (model28.B 5 ++ [step28.q]) 9000000000000 (model28.caps 5)
    (model28.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_6 : ExcludedOn (model28.B 6 ++ [step28.q]) 9000000000000 (model28.caps 6)
    (model28.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_8 : ExcludedOn (model28.B 8 ++ [step28.q]) 9000000000000 (model28.caps 8)
    (model28.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded28_3
    · exact excluded28_4
    · exact excluded28_5
    · exact excluded28_6
    · exact (hj rfl).elim
    · exact excluded28_8
    · exact excluded28_9
theorem next28 : model28.insert step28 = model29 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded29_0 : ExcludedOn (model29.B 0 ++ [step29.q]) 9000000000000 (model29.caps 0)
    (model29.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6675000000000], [75000000000]) (some (9, 2, 4))
      (some (9, 2, 4)) (.next ([6675000000000], [330000000000]) (some (9, 2, 4)) (some (9, 2, 4))
      (.next ([6630000000000], [540000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next
      ([6375000000000], [795000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next ([7845000000000],
      [990000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next ([7305000000000], [1200000000000])
      (some (9, 2, 4)) (some (9, 2, 4)) (.next ([6300000000000], [1080000000000]) (some (9, 2, 4))
      (some (9, 2, 9)) (.next ([1380000000000], [255000000000]) (some (9, 2, 9)) (some (9, 2, 9))
      (.next ([5625000000000], [1170000000000]) (some (9, 2, 9)) (some (9, 2, 9)) (.next
      ([6045000000000], [1335000000000]) (some (9, 2, 9)) (some (9, 2, 9)) (.next ([5805000000000],
      [1830000000000]) (some (9, 2, 9)) (some (9, 2, 9)) (.next ([5295000000000], [1710000000000])
      (some (7, 2, 9)) (some (7, 2, 9)) (.next ([5550000000000], [1830000000000]) (some (7, 2, 9))
      (some (7, 2, 9)) (.next ([6180000000000], [2205000000000]) (some (7, 2, 9)) (some (7, 2, 9))
      (.next ([6180000000000], [2460000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next
      ([4800000000000], [2205000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next ([5805000000000],
      [3210000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next ([630000000000], [375000000000])
      (some (7, 2, 9)) (some (7, 2, 9)) (.next ([375000000000], [375000000000]) (some (7, 2, 9))
      (some (7, 2, 9)) (.next ([2550000000000], [2955000000000]) (some (7, 2, 9)) (some (8, 2, 9))
      (.next ([1125000000000], [1710000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next
      ([210000000000], [330000000000]) (some (8, 2, 9)) (some (8, 3, 9)) (.next ([375000000000],
      [630000000000]) (some (8, 3, 9)) (some (8, 3, 9)) fan29Owner0Part1))))))))))))))))))))))))
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded29_2 : ExcludedOn (model29.B 2 ++ [step29.q]) 9000000000000 (model29.caps 2)
    (model29.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3330000000000], [75000000000]) (some (0, 0, 4))
      (some (0, 0, 4)) (.next ([6165000000000], [3165000000000]) (some (0, 0, 4)) (some (0, 1, 4))
      (.next ([2835000000000], [3090000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([1890000000000, 9000000000000], [4155000000000, 0]) (some (0, 1, 4)) (some (0, 4, 4)) (.next
      ([990000000000, 0], [3285000000000, -9000000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.next
      ([750000000000], [3330000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([990000000000],
      [5175000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0], [4155000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([-75000000000], [3405000000000]) (some (0, 4, 2)) (some (0, 4,
      3)) (.next ([-3165000000000], [9330000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-3090000000000], [5925000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-4155000000000,
      0], [6045000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3285000000000,
      9000000000000], [4275000000000, -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-3330000000000], [4080000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-5175000000000], [6165000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4,
      3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded29_3 : ExcludedOn (model29.B 3 ++ [step29.q]) 9000000000000 (model29.caps 3)
    (model29.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_4 : ExcludedOn (model29.B 4 ++ [step29.q]) 9000000000000 (model29.caps 4)
    (model29.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_5 : ExcludedOn (model29.B 5 ++ [step29.q]) 9000000000000 (model29.caps 5)
    (model29.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_6 : ExcludedOn (model29.B 6 ++ [step29.q]) 9000000000000 (model29.caps 6)
    (model29.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_7 : ExcludedOn (model29.B 7 ++ [step29.q]) 9000000000000 (model29.caps 7)
    (model29.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000], [150000000000]) (some (2, 4, 1))
      (some (3, 4, 2)) (.next ([5715000000000], [300000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([2235000000000, -9000000000000], [150000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([3825000000000], [4275000000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([1740000000000, 9000000000000], [2385000000000, -9000000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([3825000000000], [6165000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([1935000000000, -9000000000000], [6165000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([0], [1890000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-150000000000], [4275000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-300000000000],
      [6015000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-150000000000, 0], [2385000000000,
      -9000000000000]) (some (0, 4, 2)) (some (4, 4, 2)) (.next ([-4275000000000, 9000000000000],
      [8100000000000, -9000000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([-2385000000000,
      9000000000000], [4125000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-6165000000000],
      [9990000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-6165000000000, 0],
      [8100000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.terminal (some (4, 1, 2))
      (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded29_0
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6675000000000], [75000000000]) (some (9, 2, 4))
      (some (9, 2, 4)) (.next ([6675000000000], [330000000000]) (some (9, 2, 4)) (some (9, 2, 4))
      (.next ([6630000000000], [540000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next
      ([5850000000000], [525000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next ([5595000000000],
      [525000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([6375000000000], [795000000000])
      (some (7, 2, 4)) (some (7, 2, 4)) (.next ([6585000000000], [945000000000]) (some (7, 2, 4))
      (some (7, 2, 4)) (.next ([6225000000000], [900000000000]) (some (7, 2, 4)) (some (7, 2, 4))
      (.next ([6300000000000], [1080000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next
      ([1380000000000], [255000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([6225000000000],
      [1155000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([4845000000000], [900000000000])
      (some (7, 2, 4)) (some (7, 2, 4)) (.next ([6045000000000], [1155000000000]) (some (7, 2, 4))
      (some (7, 2, 4)) (.next ([5625000000000], [1170000000000]) (some (7, 2, 4)) (some (7, 2, 9))
      (.next ([6045000000000], [1335000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next
      ([5295000000000], [1710000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next ([5850000000000],
      [1905000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next ([630000000000], [375000000000])
      (some (7, 2, 9)) (some (7, 2, 9)) (.next ([375000000000], [375000000000]) (some (7, 2, 9))
      (some (7, 2, 9)) (.next ([2550000000000], [2955000000000]) (some (7, 2, 9)) (some (8, 2, 9))
      (.next ([1125000000000], [1710000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next
      ([210000000000], [330000000000]) (some (8, 2, 9)) (some (8, 3, 9)) (.next ([375000000000],
      [630000000000]) (some (8, 3, 9)) (some (8, 3, 9)) fan30Owner0Part1))))))))))))))))))))))))
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded30_2 : ExcludedOn (model30.B 2 ++ [step30.q]) 9000000000000 (model30.caps 2)
    (model30.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3330000000000], [75000000000]) (some (0, 0, 4))
      (some (0, 0, 4)) (.next ([7470000000000], [1905000000000]) (some (0, 0, 4)) (some (0, 1, 4))
      (.next ([4140000000000], [1830000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([2640000000000, 9000000000000], [1440000000000, -9000000000000]) (some (0, 1, 4)) (some (0,
      4, 4)) (.next ([2250000000000, 0], [3330000000000, -9000000000000]) (some (0, 4, 4)) (some (0,
      4, 4)) (.next ([1890000000000, 9000000000000], [4155000000000, 0]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([2250000000000], [5220000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([750000000000], [3330000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0],
      [4155000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-75000000000], [3405000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-1905000000000], [9375000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-1830000000000], [5970000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-1440000000000, 9000000000000], [4080000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-3330000000000, 9000000000000], [5580000000000, -9000000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-4155000000000, 0], [6045000000000, 9000000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-5220000000000], [7470000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-3330000000000], [4080000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some
      (0, 4, 3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded30_3 : ExcludedOn (model30.B 3 ++ [step30.q]) 9000000000000 (model30.caps 3)
    (model30.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_4 : ExcludedOn (model30.B 4 ++ [step30.q]) 9000000000000 (model30.caps 4)
    (model30.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_5 : ExcludedOn (model30.B 5 ++ [step30.q]) 9000000000000 (model30.caps 5)
    (model30.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_6 : ExcludedOn (model30.B 6 ++ [step30.q]) 9000000000000 (model30.caps 6)
    (model30.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_7 : ExcludedOn (model30.B 7 ++ [step30.q]) 9000000000000 (model30.caps 7)
    (model30.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_8 : ExcludedOn (model30.B 8 ++ [step30.q]) 9000000000000 (model30.caps 8)
    (model30.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_9 : ExcludedOn (model30.B 9 ++ [step30.q]) 9000000000000 (model30.caps 9)
    (model30.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded30_2
    · exact excluded30_3
    · exact excluded30_4
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
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_1 : ExcludedOn (model31.B 1 ++ [step31.q]) 9000000000000 (model31.caps 1)
    (model31.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_2 : ExcludedOn (model31.B 2 ++ [step31.q]) 9000000000000 (model31.caps 2)
    (model31.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_3 : ExcludedOn (model31.B 3 ++ [step31.q]) 9000000000000 (model31.caps 3)
    (model31.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6885000000000], [1545000000000]) (some (2, 0,
      1)) (some (4, 0, 1)) (.next ([3510000000000], [1545000000000]) (some (4, 0, 1)) (some (4, 0,
      1)) (.next ([1890000000000, 9000000000000], [4995000000000, -9000000000000]) (some (4, 0, 1))
      (some (4, 0, 1)) (.next ([1890000000000, 9000000000000], [5055000000000]) (some (4, 0, 1))
      (some (4, 0, 2)) (.next ([1830000000000], [5055000000000]) (some (4, 0, 2)) (some (4, 0, 2))
      (.next ([0], [5055000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([-1545000000000],
      [8430000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-1545000000000], [5055000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-4995000000000, 9000000000000], [6885000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5055000000000, 0], [6945000000000, 9000000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5055000000000], [6885000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1, 2)) (some (0, 1, 2)))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded31_4 : ExcludedOn (model31.B 4 ++ [step31.q]) 9000000000000 (model31.caps 4)
    (model31.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_5 : ExcludedOn (model31.B 5 ++ [step31.q]) 9000000000000 (model31.caps 5)
    (model31.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_6 : ExcludedOn (model31.B 6 ++ [step31.q]) 9000000000000 (model31.caps 6)
    (model31.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_7 : ExcludedOn (model31.B 7 ++ [step31.q]) 9000000000000 (model31.caps 7)
    (model31.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_9 : ExcludedOn (model31.B 9 ++ [step31.q]) 9000000000000 (model31.caps 9)
    (model31.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded31_5
    · exact excluded31_6
    · exact excluded31_7
    · exact (hj rfl).elim
    · exact excluded31_9
theorem next31 : model31.insert step31 = model32 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext210000220000
end ConwaySoifer.Simplified.Certificates
