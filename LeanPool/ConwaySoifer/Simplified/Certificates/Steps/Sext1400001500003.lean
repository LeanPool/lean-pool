/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext140000150000
import Mathlib.Tactic.FinCases

/-!
# Sext 140000 150000 3

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
namespace Sext140000150000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner0Part0 : FanWitness := (.next ([-2325000000000], [8250000000000]) (some (8, 3, 5))
    (some (8, 3, 5)) (.next ([-2145000000000], [7530000000000]) (some (8, 3, 5)) (some (8, 3, 5))
    (.next ([-210000000000], [465000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next
    ([-420000000000], [840000000000]) (some (8, 3, 5)) (some (8, 4, 5)) (.next ([-777000000000,
    -2550000000000], [1464000000000, 5100000000000]) (some (8, 4, 5)) (some (8, 4, 6)) (.next
    ([-420000000000], [750000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-3795000000000],
    [5640000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-4080000000000], [5670000000000])
    (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-4455000000000], [5970000000000]) (some (8, 4, 6))
    (some (8, 4, 6)) (.next ([-4545000000000], [5970000000000]) (some (8, 4, 6)) (some (8, 4, 6))
    (.next ([-4740000000000], [6000000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next
    ([-4335000000000], [5460000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-4830000000000],
    [6000000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-7785000000000], [9375000000000])
    (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-4995000000000], [5790000000000]) (some (8, 4, 6))
    (some (8, 4, 6)) (.next ([-5085000000000], [5790000000000]) (some (8, 4, 6)) (some (8, 4, 6))
    (.next ([-4875000000000], [5550000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next
    ([-7008000000000, 2550000000000], [7911000000000, -5100000000000]) (some (8, 4, 6)) (some (8, 4,
    6)) (.next ([-255000000000], [285000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next
    ([-8115000000000], [9045000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-8115000000000],
    [8955000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-5160000000000], [5580000000000])
    (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-7695000000000], [8205000000000]) (some (8, 4, 6))
    (some (8, 4, 6)) (.next ([-1107000000000, -2550000000000], [1134000000000, 5100000000000]) (some
    (8, 4, 6)) (some (8, 4, 6)) (.terminal (some (8, 4, 6)) (some (8, 4, 6)) (some (8, 4,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner0Part1 : FanWitness := (.next ([1845000000000], [3795000000000]) (some (0, 8, 4))
    (some (0, 8, 4)) (.next ([1590000000000], [4080000000000]) (some (0, 8, 4)) (some (0, 8, 4))
    (.next ([1515000000000], [4455000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next
    ([1425000000000], [4545000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([1260000000000],
    [4740000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([1125000000000], [4335000000000])
    (some (0, 8, 4)) (some (0, 8, 4)) (.next ([1170000000000], [4830000000000]) (some (0, 8, 4))
    (some (0, 8, 5)) (.next ([1590000000000], [7785000000000]) (some (0, 8, 5)) (some (0, 8, 5))
    (.next ([795000000000], [4995000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next
    ([705000000000], [5085000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next ([675000000000],
    [4875000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next ([903000000000, -2550000000000],
    [7008000000000, -2550000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next ([30000000000],
    [255000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next ([930000000000], [8115000000000]) (some
    (0, 8, 5)) (some (0, 8, 5)) (.next ([840000000000], [8115000000000]) (some (0, 8, 5)) (some (0,
    8, 5)) (.next ([420000000000], [5160000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next
    ([510000000000], [7695000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next ([27000000000,
    2550000000000], [1107000000000, 2550000000000]) (some (0, 8, 5)) (some (8, 8, 5)) (.next ([0],
    [90000000000]) (some (8, 8, 5)) (some (8, 8, 5)) (.next ([-45000000000], [5415000000000]) (some
    (8, 8, 5)) (some (8, 8, 5)) (.next ([-63000000000, 2550000000000], [1107000000000,
    2550000000000]) (some (8, 8, 5)) (some (8, 8, 5)) (.next ([-339000000000, -5100000000000],
    [5022000000000, 2550000000000]) (some (8, 8, 5)) (some (8, 8, 5)) (.next ([-180000000000],
    [720000000000]) (some (8, 8, 5)) (some (8, 8, 5)) (.next ([-2115000000000], [7785000000000])
    (some (8, 8, 5)) (some (8, 8, 5)) fan24Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner4Part0 : FanWitness := (.next ([5040000000000], [375000000000]) (some (4, 1, 5)) (some
    (4, 1, 5)) (.next ([1860000000000], [375000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([375000000000], [90000000000]) (some (4, 1, 5)) (some (4, 5, 5)) (.next ([3000000000000],
    [2085000000000]) (some (4, 5, 5)) (some (4, 5, 5)) (.next ([2625000000000], [1995000000000])
    (some (4, 5, 5)) (some (4, 5, 5)) (.next ([1680000000000, 9000000000000], [1740000000000,
    -9000000000000]) (some (4, 5, 5)) (some (4, 5, 5)) (.next ([2625000000000], [4320000000000])
    (some (4, 5, 5)) (some (4, 5, 5)) (.next ([1260000000000, 9000000000000], [5505000000000]) (some
    (4, 5, 3)) (some (4, 5, 3)) (.next ([885000000000, 9000000000000], [5415000000000]) (some (4, 5,
    3)) (some (4, 5, 3)) (.next ([420000000000], [3000000000000]) (some (4, 5, 3)) (some (4, 5, 3))
    (.next ([885000000000, 9000000000000], [7740000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([0], [5505000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([-375000000000],
    [7740000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-375000000000], [5415000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-375000000000], [2235000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-90000000000], [465000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-2085000000000], [5085000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-1995000000000], [4620000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1740000000000,
    9000000000000], [3420000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4320000000000],
    [6945000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next ([-5505000000000], [6765000000000,
    9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-5415000000000], [6300000000000,
    9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3000000000000], [3420000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-7740000000000], [8625000000000, 9000000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5, 4)) (some (0, 5, 4)) (some (0, 5,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner0Part0 : FanWitness := (.next ([-90000000000], [1170000000000]) (some (8, 3, 5)) (some
    (8, 3, 5)) (.next ([-750000000000], [5850000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next
    ([-750000000000], [5760000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-180000000000],
    [720000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-210000000000], [465000000000]) (some
    (8, 3, 5)) (some (8, 3, 5)) (.next ([-4335000000000], [9555000000000]) (some (8, 3, 5)) (some
    (8, 4, 5)) (.next ([-4590000000000], [9840000000000]) (some (8, 4, 5)) (some (8, 4, 5)) (.next
    ([-420000000000], [840000000000]) (some (8, 4, 5)) (some (8, 4, 5)) (.next ([-5055000000000],
    [10095000000000]) (some (8, 4, 5)) (some (8, 4, 6)) (.next ([-777000000000, -2550000000000],
    [1464000000000, 5100000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-420000000000],
    [750000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-3795000000000], [5640000000000])
    (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-4080000000000], [5670000000000]) (some (8, 4, 6))
    (some (8, 4, 6)) (.next ([-4455000000000], [5970000000000]) (some (8, 4, 6)) (some (8, 4, 6))
    (.next ([-4545000000000], [5970000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next
    ([-4740000000000], [6000000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-4335000000000],
    [5460000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-4830000000000], [6000000000000])
    (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-4995000000000], [5790000000000]) (some (8, 4, 6))
    (some (8, 4, 6)) (.next ([-5085000000000], [5790000000000]) (some (8, 4, 6)) (some (8, 4, 6))
    (.next ([-4875000000000], [5550000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next
    ([-255000000000], [285000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-5160000000000],
    [5580000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-1107000000000, -2550000000000],
    [1134000000000, 5100000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.terminal (some (8, 4, 6))
    (some (8, 4, 6)) (some (8, 4, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner0Part1 : FanWitness := (.next ([5220000000000], [4335000000000]) (some (8, 8, 4))
    (some (8, 8, 4)) (.next ([5250000000000], [4590000000000]) (some (8, 2, 4)) (some (8, 2, 4))
    (.next ([420000000000], [420000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
    ([5040000000000], [5055000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([687000000000,
    2550000000000], [777000000000, 2550000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
    ([330000000000], [420000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([1845000000000],
    [3795000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([1590000000000], [4080000000000])
    (some (8, 2, 4)) (some (8, 2, 4)) (.next ([1515000000000], [4455000000000]) (some (8, 2, 4))
    (some (8, 2, 4)) (.next ([1425000000000], [4545000000000]) (some (8, 2, 4)) (some (8, 2, 4))
    (.next ([1260000000000], [4740000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
    ([1125000000000], [4335000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([1170000000000],
    [4830000000000]) (some (8, 2, 4)) (some (8, 2, 5)) (.next ([795000000000], [4995000000000])
    (some (8, 2, 5)) (some (8, 2, 5)) (.next ([705000000000], [5085000000000]) (some (8, 2, 5))
    (some (8, 2, 5)) (.next ([675000000000], [4875000000000]) (some (8, 2, 5)) (some (8, 2, 5))
    (.next ([30000000000], [255000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([420000000000],
    [5160000000000]) (some (8, 2, 5)) (some (8, 3, 5)) (.next ([27000000000, 2550000000000],
    [1107000000000, 2550000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([0], [90000000000])
    (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-45000000000], [5415000000000]) (some (8, 3, 5))
    (some (8, 3, 5)) (.next ([-63000000000, 2550000000000], [1107000000000, 2550000000000]) (some
    (8, 3, 5)) (some (8, 3, 5)) (.next ([-330000000000], [5010000000000]) (some (8, 3, 5)) (some (8,
    3, 5)) (.next ([-420000000000], [6180000000000]) (some (8, 3, 5)) (some (8, 3, 5))
    fan27Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner3Part0 : FanWitness := (.next ([2610000000000, -9000000000000], [630000000000]) (some
    (4, 5, 2)) (some (4, 5, 2)) (.next ([6690000000000, 9000000000000], [2310000000000,
    -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([5430000000000], [3570000000000])
    (some (4, 5, 2)) (some (4, 5, 2)) (.next ([4170000000000, -9000000000000], [3570000000000])
    (some (4, 5, 2)) (some (4, 5, 2)) (.next ([1260000000000, 9000000000000], [1260000000000,
    9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([2010000000000, 9000000000000],
    [2700000000000, -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([1560000000000],
    [2940000000000]) (some (4, 5, 2)) (some (4, 5, 3)) (.next ([750000000000], [3960000000000])
    (some (4, 5, 3)) (some (4, 5, 3)) (.next ([630000000000, 9000000000000], [4500000000000]) (some
    (4, 5, 3)) (some (4, 5, 3)) (.next ([390000000000], [4290000000000]) (some (4, 5, 3)) (some (4,
    5, 3)) (.next ([210000000000], [3120000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0],
    [1260000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([-630000000000],
    [4500000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-630000000000], [3240000000000,
    -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2310000000000, 9000000000000],
    [9000000000000]) (some (0, 5, 3)) (some (1, 5, 3)) (.next ([-3570000000000], [9000000000000])
    (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-3570000000000], [7740000000000, -9000000000000])
    (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-1260000000000, -9000000000000], [2520000000000,
    18000000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-2700000000000, 9000000000000],
    [4710000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-2940000000000], [4500000000000])
    (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-3960000000000], [4710000000000]) (some (1, 5, 3))
    (some (5, 5, 3)) (.next ([-4500000000000, 0], [5130000000000, 9000000000000]) (some (5, 5, 3))
    (some (5, 5, 3)) (.next ([-4290000000000], [4680000000000]) (some (5, 5, 3)) (some (5, 5, 3))
    (.next ([-3120000000000], [3330000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.terminal (some
    (5, 2, 3)) (some (5, 2, 3)) (some (5, 2, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan29Owner4Part0 : FanWitness := (.next ([375000000000], [90000000000]) (some (4, 1, 5)) (some
    (4, 1, 5)) (.next ([3570000000000], [1935000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([3195000000000], [1845000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([3210000000000],
    [4620000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([3120000000000], [5085000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1260000000000, 9000000000000], [2310000000000,
    -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1680000000000, 9000000000000],
    [6945000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1260000000000,
    9000000000000], [5505000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([885000000000,
    9000000000000], [5415000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([420000000000],
    [4635000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([420000000000], [8205000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0], [5505000000000]) (some (4, 1, 5)) (some (4, 1,
    5)) (.next ([-375000000000], [5415000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-90000000000], [465000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1935000000000],
    [5505000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1845000000000], [5040000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4620000000000], [7830000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-5085000000000], [8205000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-2310000000000, 9000000000000], [3570000000000]) (some (0, 1, 5)) (some (0, 5, 5))
    (.next ([-6945000000000, 9000000000000], [8625000000000]) (some (0, 5, 5)) (some (0, 5, 5))
    (.next ([-5505000000000], [6765000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-5415000000000], [6300000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-4635000000000], [5055000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-8205000000000], [8625000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5,
    4)) (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

theorem excluded24_0 : ExcludedOn (model24.B 0 ++ [step24.q]) 9000000000000 (model24.caps 0)
    (model24.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5370000000000], [45000000000]) (some (6, 8, 4))
      (some (7, 8, 4)) (.next ([1044000000000, 5100000000000], [63000000000, -2550000000000]) (some
      (7, 8, 4)) (some (7, 8, 4)) (.next ([4683000000000, -2550000000000], [339000000000,
      5100000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([540000000000], [180000000000])
      (some (7, 8, 4)) (some (7, 8, 4)) (.next ([5670000000000], [2115000000000]) (some (7, 8, 4))
      (some (7, 8, 4)) (.next ([5925000000000], [2325000000000]) (some (7, 8, 4)) (some (7, 8, 4))
      (.next ([5385000000000], [2145000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next
      ([255000000000], [210000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([420000000000],
      [420000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([687000000000, 2550000000000],
      [777000000000, 2550000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([330000000000],
      [420000000000]) (some (7, 8, 4)) (some (7, 8, 4)) fan24Owner0Part1)))))))))))) (den :=
      9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_4 : ExcludedOn (model24.B 4 ++ [step24.q]) 9000000000000 (model24.caps 4)
    (model24.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7365000000000], [375000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) fan24Owner4Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_6 : ExcludedOn (model24.B 6 ++ [step24.q]) 9000000000000 (model24.caps 6)
    (model24.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded24_0
    · exact excluded24_1
    · exact excluded24_2
    · exact excluded24_3
    · exact excluded24_4
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.witnessedFan (.next ([3450000000000, -9000000000000], [510000000000,
      9000000000000]) (some (3, 5, 2)) (some (5, 5, 2)) (.next ([3150000000000], [975000000000])
      (some (5, 5, 2)) (some (5, 5, 2)) (.next ([1890000000000, -9000000000000], [975000000000])
      (some (5, 5, 2)) (some (5, 5, 2)) (.next ([4125000000000], [2700000000000]) (some (5, 5, 2))
      (some (5, 5, 2)) (.next ([1260000000000, 9000000000000], [1260000000000, 9000000000000]) (some
      (5, 1, 2)) (some (5, 1, 2)) (.next ([4710000000000], [5100000000000]) (some (5, 1, 2)) (some
      (5, 1, 2)) (.next ([2010000000000, 9000000000000], [2700000000000, -9000000000000]) (some (5,
      1, 2)) (some (5, 1, 2)) (.next ([1260000000000, 9000000000000], [4590000000000,
      -9000000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next ([585000000000], [2400000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([750000000000], [3960000000000]) (some (5, 1, 3))
      (some (5, 2, 3)) (.next ([285000000000, 9000000000000], [4125000000000]) (some (5, 2, 3))
      (some (5, 2, 3)) (.next ([0], [1260000000000, 9000000000000]) (some (5, 2, 3)) (some (5, 2,
      3)) (.next ([-510000000000, -9000000000000], [3960000000000]) (some (5, 2, 3)) (some (5, 2,
      3)) (.next ([-975000000000], [4125000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-975000000000], [2865000000000, -9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-2700000000000], [6825000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-1260000000000,
      -9000000000000], [2520000000000, 18000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-5100000000000], [9810000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-2700000000000,
      9000000000000], [4710000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-4590000000000,
      9000000000000], [5850000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-2400000000000],
      [2985000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-3960000000000], [4710000000000])
      (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-4125000000000, 0], [4410000000000, 9000000000000])
      (some (5, 2, 3)) (some (5, 2, 3)) (.terminal (some (5, 2, 3)) (some (5, 2, 3)) (some (5, 2,
      3))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded25_4 : ExcludedOn (model25.B 4 ++ [step25.q]) 9000000000000 (model25.caps 4)
    (model25.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_5 : ExcludedOn (model25.B 5 ++ [step25.q]) 9000000000000 (model25.caps 5)
    (model25.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 2 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded26_4 : ExcludedOn (model26.B 4 ++ [step26.q]) 9000000000000 (model26.caps 4)
    (model26.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5040000000000], [375000000000]) (some (5, 0, 1))
      (some (5, 1, 1)) (.next ([375000000000], [90000000000]) (some (5, 1, 1)) (some (5, 1, 1))
      (.next ([3000000000000], [2085000000000]) (some (5, 1, 1)) (some (5, 1, 2)) (.next
      ([2625000000000], [1995000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([5130000000000],
      [4875000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next ([4755000000000], [4785000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2130000000000], [2790000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([1260000000000, 9000000000000], [5505000000000]) (some (5, 1, 3))
      (some (5, 1, 5)) (.next ([630000000000], [3240000000000, -9000000000000]) (some (5, 1, 5))
      (some (5, 1, 5)) (.next ([885000000000, 9000000000000], [5415000000000]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([420000000000], [3000000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([0], [5505000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([-375000000000],
      [5415000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-90000000000], [465000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2085000000000], [5085000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([-1995000000000], [4620000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([-4875000000000], [10005000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-4785000000000], [9540000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-2790000000000], [4920000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-5505000000000], [6765000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-3240000000000, 9000000000000], [3870000000000, -9000000000000]) (some (0, 1, 5)) (some (0,
      1, 5)) (.next ([-5415000000000], [6300000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1,
      5)) (.next ([-3000000000000], [3420000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.terminal
      (some (0, 1, 5)) (some (0, 1, 5)) (some (0, 1, 5))))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded26_5 : ExcludedOn (model26.B 5 ++ [step26.q]) 9000000000000 (model26.caps 5)
    (model26.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4170000000000], [960000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([4500000000000], [1980000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([3150000000000], [2310000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([4500000000000], [5130000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [5460000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-960000000000], [5130000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1980000000000], [6480000000000]) (some (0, 1, 3))
      (some (0, 3, 3)) (.next ([-2310000000000], [5460000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-5130000000000], [9630000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
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
    · exact (hj rfl).elim
    · exact excluded26_4
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5370000000000], [45000000000]) (some (6, 8, 4))
      (some (7, 8, 4)) (.next ([1044000000000, 5100000000000], [63000000000, -2550000000000]) (some
      (7, 8, 4)) (some (7, 8, 4)) (.next ([4680000000000], [330000000000]) (some (7, 8, 4)) (some
      (7, 8, 4)) (.next ([5760000000000], [420000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next
      ([1080000000000], [90000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([5100000000000],
      [750000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([5010000000000], [750000000000])
      (some (7, 8, 4)) (some (7, 8, 4)) (.next ([540000000000], [180000000000]) (some (7, 8, 4))
      (some (8, 8, 4)) (.next ([255000000000], [210000000000]) (some (8, 8, 4)) (some (8, 8, 4))
      fan27Owner0Part1)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([3870000000000], [630000000000]) (some (3, 5, 2))
      (some (4, 5, 2)) fan27Owner3Part0)) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_5 : ExcludedOn (model27.B 5 ++ [step27.q]) 9000000000000 (model27.caps 5)
    (model27.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded27_3
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 2 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_1 : ExcludedOn (model28.B 1 ++ [step28.q]) 9000000000000 (model28.caps 1)
    (model28.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7635000000000, 9000000000000], [1890000000000,
      -9000000000000]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([6375000000000], [3150000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([5115000000000, -9000000000000], [3150000000000, 0])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1260000000000, 9000000000000], [1260000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [1260000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1890000000000, 9000000000000],
      [9525000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-3150000000000], [9525000000000])
      (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-3150000000000, 0], [8265000000000,
      -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1260000000000, -9000000000000],
      [2520000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 3)) (.terminal (some (3, 1, 3))
      (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded28_3 : ExcludedOn (model28.B 3 ++ [step28.q]) 9000000000000 (model28.caps 3)
    (model28.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3870000000000], [630000000000]) (some (3, 1, 5))
      (some (4, 1, 5)) (.next ([7845000000000], [1875000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([2610000000000, -9000000000000], [630000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([4515000000000], [2085000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([1260000000000, 9000000000000], [1260000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1,
      5)) (.next ([2010000000000, 9000000000000], [2700000000000, -9000000000000]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([2625000000000, 0], [4590000000000, -9000000000000]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([2625000000000], [5850000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([750000000000], [3960000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([630000000000, 9000000000000], [4500000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([210000000000], [3120000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0],
      [1260000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 2, 5)) (.next ([-630000000000],
      [4500000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1875000000000], [9720000000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-630000000000], [3240000000000, -9000000000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2085000000000], [6600000000000]) (some (0, 2, 5))
      (some (1, 2, 5)) (.next ([-1260000000000, -9000000000000], [2520000000000, 18000000000000])
      (some (1, 2, 5)) (some (1, 5, 5)) (.next ([-2700000000000, 9000000000000], [4710000000000])
      (some (1, 5, 5)) (some (1, 5, 5)) (.next ([-4590000000000, 9000000000000], [7215000000000,
      -9000000000000]) (some (1, 5, 5)) (some (1, 5, 5)) (.next ([-5850000000000], [8475000000000])
      (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-3960000000000], [4710000000000]) (some (1, 5, 3))
      (some (1, 5, 3)) (.next ([-4500000000000, 0], [5130000000000, 9000000000000]) (some (1, 5, 3))
      (some (1, 5, 3)) (.next ([-3120000000000], [3330000000000]) (some (1, 5, 3)) (some (1, 5, 3))
      (.terminal (some (1, 5, 3)) (some (1, 5, 3)) (some (1, 5, 3))))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded28_4 : ExcludedOn (model28.B 4 ++ [step28.q]) 9000000000000 (model28.caps 4)
    (model28.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_5 : ExcludedOn (model28.B 5 ++ [step28.q]) 9000000000000 (model28.caps 5)
    (model28.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_6 : ExcludedOn (model28.B 6 ++ [step28.q]) 9000000000000 (model28.caps 6)
    (model28.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_7 : ExcludedOn (model28.B 7 ++ [step28.q]) 9000000000000 (model28.caps 7)
    (model28.ord 7) 0 1 100 := by
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
    · exact (hj rfl).elim
    · exact excluded28_3
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_2 : ExcludedOn (model29.B 2 ++ [step29.q]) 9000000000000 (model29.caps 2)
    (model29.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_3 : ExcludedOn (model29.B 3 ++ [step29.q]) 9000000000000 (model29.caps 3)
    (model29.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_4 : ExcludedOn (model29.B 4 ++ [step29.q]) 9000000000000 (model29.caps 4)
    (model29.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5040000000000], [375000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) fan29Owner4Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded29_5 : ExcludedOn (model29.B 5 ++ [step29.q]) 9000000000000 (model29.caps 5)
    (model29.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (1475) (3132) (313200) (.witnessedFan (.next
      ([8205000000000], [375000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([375000000000],
      [1260000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1635000000000], [6357000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1473000000000], [7107000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([1260000000000, 9000000000000], [6732000000000, 0]) (some (4, 1, 2))
      (some (4, 1, 4)) (.next ([885000000000], [6945000000000]) (some (4, 1, 4)) (some (4, 1, 4))
      (.next ([885000000000, 9000000000000], [7320000000000, -9000000000000]) (some (3, 1, 4)) (some
      (3, 1, 4)) (.next ([0, 9000000000000], [375000000000, -9000000000000]) (some (3, 1, 4)) (some
      (3, 1, 4)) (.next ([0, 0], [1260000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-375000000000], [8580000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next
      ([-1260000000000], [1635000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-6357000000000], [7992000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-7107000000000], [8580000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-6732000000000,
      0], [7992000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-6945000000000], [7830000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-7320000000000,
      9000000000000], [8205000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-375000000000,
      9000000000000], [375000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (.witnessedFan (.next
      ([8205000000000], [375000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([375000000000],
      [1260000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1635000000000], [6357000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1473000000000], [7107000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([1260000000000, 9000000000000], [6732000000000, 0]) (some (4, 1, 2))
      (some (4, 1, 4)) (.next ([885000000000, 9000000000000], [7320000000000, -9000000000000]) (some
      (4, 1, 4)) (some (4, 1, 4)) (.next ([885000000000], [6945000000000]) (some (0, 1, 4)) (some
      (0, 1, 4)) (.next ([0, 0], [1260000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-375000000000], [8580000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next
      ([-1260000000000], [1635000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-6357000000000], [7992000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-7107000000000], [8580000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-6732000000000,
      0], [7992000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-7320000000000,
      9000000000000], [8205000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-6945000000000], [7830000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4)))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded29_6 : ExcludedOn (model29.B 6 ++ [step29.q]) 9000000000000 (model29.caps 6)
    (model29.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded30_1 : ExcludedOn (model30.B 1 ++ [step30.q]) 9000000000000 (model30.caps 1)
    (model30.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5085000000000], [3915000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([1260000000000, 9000000000000], [1260000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([5085000000000], [5175000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([3825000000000, -9000000000000], [6435000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [1260000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-3915000000000, 9000000000000],
      [9000000000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-1260000000000,
      -9000000000000], [2520000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-5175000000000], [10260000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-6435000000000, -9000000000000], [10260000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0))
      (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded30_2 : ExcludedOn (model30.B 2 ++ [step30.q]) 9000000000000 (model30.caps 2)
    (model30.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_3 : ExcludedOn (model30.B 3 ++ [step30.q]) 9000000000000 (model30.caps 3)
    (model30.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_4 : ExcludedOn (model30.B 4 ++ [step30.q]) 9000000000000 (model30.caps 4)
    (model30.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_5 : ExcludedOn (model30.B 5 ++ [step30.q]) 9000000000000 (model30.caps 5)
    (model30.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5175000000000], [2190000000000]) (some (4, 0,
      2)) (some (4, 1, 2)) (.next ([5175000000000, 9000000000000], [2565000000000, -9000000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([3915000000000], [3825000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([1008000000000], [2817000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([375000000000], [1260000000000]) (some (3, 1, 2)) (some (3, 1, 4)) (.next
      ([1635000000000], [6357000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([1260000000000,
      9000000000000], [6732000000000, 0]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0, 0],
      [1260000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([-2190000000000],
      [7365000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-2565000000000, 9000000000000],
      [7740000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-3825000000000],
      [7740000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2817000000000], [3825000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1260000000000], [1635000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-6357000000000], [7992000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-6732000000000, 0], [7992000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded30_6 : ExcludedOn (model30.B 6 ++ [step30.q]) 9000000000000 (model30.caps 6)
    (model30.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3825000000000], [1260000000000]) (some (2, 0,
      1)) (some (2, 0, 2)) (.next ([5085000000000], [3915000000000, -9000000000000]) (some (2, 0,
      2)) (some (2, 0, 2)) (.next ([1260000000000, 9000000000000], [7740000000000, -9000000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([0, 9000000000000], [3825000000000, -9000000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1260000000000, 9000000000000]) (some (3, 0,
      2)) (some (3, 0, 2)) (.next ([-1260000000000], [5085000000000]) (some (3, 0, 2)) (some (3, 1,
      2)) (.next ([-3915000000000, 9000000000000], [9000000000000, -9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-7740000000000, 9000000000000], [9000000000000, 0]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-3825000000000, 9000000000000], [3825000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded30_1
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

theorem excluded31_1 : ExcludedOn (model31.B 1 ++ [step31.q]) 9000000000000 (model31.caps 1)
    (model31.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_2 : ExcludedOn (model31.B 2 ++ [step31.q]) 9000000000000 (model31.caps 2)
    (model31.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_3 : ExcludedOn (model31.B 3 ++ [step31.q]) 9000000000000 (model31.caps 3)
    (model31.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_4 : ExcludedOn (model31.B 4 ++ [step31.q]) 9000000000000 (model31.caps 4)
    (model31.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_5 : ExcludedOn (model31.B 5 ++ [step31.q]) 9000000000000 (model31.caps 5)
    (model31.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6000000000000], [1365000000000]) (some (4, 0,
      2)) (some (4, 1, 2)) (.next ([6000000000000, 9000000000000], [1740000000000, -9000000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([4740000000000], [3000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([1008000000000], [1992000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([375000000000], [1260000000000]) (some (3, 1, 2)) (some (3, 1, 4)) (.next
      ([1635000000000], [6357000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([1260000000000,
      9000000000000], [6732000000000, 0]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0, 0],
      [1260000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([-1365000000000],
      [7365000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1740000000000, 9000000000000],
      [7740000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-3000000000000],
      [7740000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1992000000000], [3000000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1260000000000], [1635000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-6357000000000], [7992000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-6732000000000, 0], [7992000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded31_6 : ExcludedOn (model31.B 6 ++ [step31.q]) 9000000000000 (model31.caps 6)
    (model31.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3000000000000], [1260000000000]) (some (2, 0,
      1)) (some (2, 0, 2)) (.next ([4260000000000], [4740000000000, -9000000000000]) (some (2, 0,
      2)) (some (2, 0, 2)) (.next ([1260000000000, 9000000000000], [7740000000000, -9000000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([0, 9000000000000], [3000000000000, -9000000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1260000000000, 9000000000000]) (some (3, 0,
      2)) (some (3, 0, 2)) (.next ([-1260000000000], [4260000000000]) (some (3, 0, 2)) (some (3, 1,
      2)) (.next ([-4740000000000, 9000000000000], [9000000000000, -9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-7740000000000, 9000000000000], [9000000000000, 0]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-3000000000000, 9000000000000], [3000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded31_1
    · exact excluded31_2
    · exact excluded31_3
    · exact excluded31_4
    · exact excluded31_5
    · exact excluded31_6
    · exact excluded31_7
    · exact excluded31_8
    · exact excluded31_9
theorem next31 : model31.insert step31 = model32 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext140000150000
end ConwaySoifer.Simplified.Certificates
