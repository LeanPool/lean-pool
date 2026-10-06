/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint180000190000
import Mathlib.Tactic.FinCases

/-!
# Sint 180000 190000 4

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
namespace Sint180000190000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner0Part0 : FanWitness := (.next ([-345000000000], [6540000000000]) (some (8, 4, 6))
    (some (8, 4, 6)) (.next ([-540000000000], [6645000000000]) (some (8, 4, 6)) (some (8, 4, 6))
    (.next ([-165000000000], [1455000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next
    ([-750000000000], [3075000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-375000000000],
    [915000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-334800000000, -4860000000000],
    [812400000000, 2430000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-90000000000],
    [195000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-375000000000], [750000000000]) (some
    (8, 4, 6)) (some (8, 4, 7)) (.next ([-499800000000, -4860000000000], [977400000000,
    2430000000000]) (some (8, 4, 7)) (some (8, 5, 7)) (.next ([-6375000000000], [10185000000000])
    (some (8, 5, 7)) (some (8, 5, 7)) (.next ([-6480000000000], [10095000000000]) (some (8, 5, 7))
    (some (8, 5, 7)) (.next ([-5625000000000], [7110000000000]) (some (8, 5, 7)) (some (8, 5, 7))
    (.next ([-5730000000000], [7020000000000]) (some (8, 5, 7)) (some (8, 5, 7)) (.next
    ([-3075000000000], [3615000000000]) (some (8, 5, 7)) (some (8, 5, 7)) (.next ([-6375000000000],
    [7485000000000]) (some (8, 5, 7)) (some (8, 5, 7)) (.next ([-3240000000000], [3780000000000])
    (some (8, 5, 7)) (some (8, 5, 7)) (.next ([-6437400000000, -2430000000000], [7444800000000,
    4860000000000]) (some (8, 5, 7)) (some (8, 5, 7)) (.next ([-6480000000000], [7395000000000])
    (some (8, 5, 7)) (some (8, 5, 7)) (.next ([-1290000000000], [1455000000000]) (some (8, 5, 7))
    (some (8, 5, 7)) (.next ([-6542400000000, -2430000000000], [7354800000000, 4860000000000]) (some
    (8, 5, 7)) (some (8, 5, 7)) (.next ([-1249800000000, -4860000000000], [1352400000000,
    2430000000000]) (some (8, 5, 7)) (some (8, 5, 7)) (.next ([-3990000000000], [4155000000000])
    (some (8, 5, 7)) (some (8, 5, 7)) (.next ([-6915000000000], [7110000000000]) (some (8, 5, 7))
    (some (8, 5, 7)) (.next ([-6915000000000], [6945000000000]) (some (8, 5, 7)) (some (8, 5, 7))
    (.terminal (some (8, 5, 7)) (some (8, 5, 7)) (some (8, 5, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner0Part1 : FanWitness := (.next ([1290000000000], [165000000000]) (some (7, 8, 6)) (some
    (7, 8, 6)) (.next ([2325000000000], [750000000000]) (some (7, 8, 6)) (some (7, 8, 6)) (.next
    ([540000000000], [375000000000]) (some (7, 8, 6)) (some (7, 8, 6)) (.next ([477600000000,
    -2430000000000], [334800000000, 4860000000000]) (some (7, 8, 6)) (some (7, 8, 6)) (.next
    ([105000000000], [90000000000]) (some (7, 8, 6)) (some (7, 8, 6)) (.next ([375000000000],
    [375000000000]) (some (7, 8, 6)) (some (7, 8, 6)) (.next ([477600000000, -2430000000000],
    [499800000000, 4860000000000]) (some (7, 8, 6)) (some (7, 8, 6)) (.next ([3810000000000],
    [6375000000000]) (some (7, 8, 6)) (some (7, 8, 6)) (.next ([3615000000000], [6480000000000])
    (some (7, 8, 6)) (some (7, 8, 6)) (.next ([1485000000000], [5625000000000]) (some (7, 8, 6))
    (some (8, 8, 6)) (.next ([1290000000000], [5730000000000]) (some (8, 8, 6)) (some (8, 8, 6))
    (.next ([540000000000], [3075000000000]) (some (8, 8, 6)) (some (8, 8, 6)) (.next
    ([1110000000000], [6375000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([540000000000],
    [3240000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([1007400000000, 2430000000000],
    [6437400000000, 2430000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([915000000000],
    [6480000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([165000000000], [1290000000000])
    (some (8, 3, 6)) (some (8, 3, 6)) (.next ([812400000000, 2430000000000], [6542400000000,
    2430000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([102600000000, -2430000000000],
    [1249800000000, 4860000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([165000000000],
    [3990000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([195000000000], [6915000000000])
    (some (8, 3, 6)) (some (8, 3, 6)) (.next ([30000000000], [6915000000000]) (some (8, 3, 6)) (some
    (8, 3, 6)) (.next ([0], [1290000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
    ([-165000000000], [7020000000000]) (some (8, 3, 6)) (some (8, 4, 6))
    fan33Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner5Part0 : FanWitness := (.next ([5265000000000, 0], [495000000000, 9000000000000])
    (some (5, 1, 2)) (some (5, 1, 2)) (.next ([4710000000000], [540000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([5250000000000, 0], [1620000000000, 9000000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([5385000000000], [3240000000000]) (some (5, 1, 2)) (some (5, 1, 2))
    (.next ([3090000000000, -9000000000000], [2160000000000, 9000000000000]) (some (5, 1, 2)) (some
    (5, 1, 2)) (.next ([3765000000000, -9000000000000], [4860000000000, 9000000000000]) (some (5, 1,
    2)) (some (5, 1, 3)) (.next ([2010000000000], [3375000000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([1125000000000], [4140000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([900000000000], [3360000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([675000000000],
    [2700000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([15000000000], [3585000000000]) (some
    (0, 1, 3)) (some (0, 1, 5)) (.next ([0], [5250000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-15000000000], [1125000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
    ([-495000000000, -9000000000000], [5760000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2,
    5)) (.next ([-540000000000], [5250000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1620000000000, -9000000000000], [6870000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2,
    5)) (.next ([-3240000000000], [8625000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-2160000000000, -9000000000000], [5250000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-4860000000000, -9000000000000], [8625000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-3375000000000], [5385000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4140000000000],
    [5265000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3360000000000], [4260000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2700000000000], [3375000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-3585000000000], [3600000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner3Part0 : FanWitness := (.next ([5760000000000], [735000000000, 9000000000000]) (some
    (4, 0, 5)) (some (4, 1, 5)) (.next ([6210000000000], [1620000000000, 9000000000000]) (some (4,
    1, 5)) (some (4, 1, 5)) (.next ([5010000000000], [1485000000000]) (some (4, 1, 5)) (some (4, 1,
    5)) (.next ([2955000000000], [1170000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([5460000000000], [2370000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1620000000000],
    [750000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([4125000000000], [3255000000000])
    (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1620000000000], [1620000000000]) (some (4, 1, 3))
    (some (4, 1, 3)) (.next ([450000000000], [885000000000]) (some (4, 1, 3)) (some (4, 1, 3))
    (.next ([1755000000000], [4875000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
    ([885000000000], [4875000000000]) (some (4, 1, 3)) (some (4, 5, 3)) (.next ([0], [1620000000000,
    9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0, -9000000000000], [750000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-735000000000, -9000000000000], [6495000000000,
    9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1620000000000, -9000000000000],
    [7830000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1485000000000],
    [6495000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1170000000000], [4125000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2370000000000], [7830000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-750000000000], [2370000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-3255000000000], [7380000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-1620000000000], [3240000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-885000000000],
    [1335000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4875000000000], [6630000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4875000000000], [5760000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5,
    3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner6Part0 : FanWitness := (.next ([3240000000000], [750000000000]) (some (5, 5, 3)) (some
    (5, 5, 3)) (.next ([5274000000000, 0], [2520000000000, -9000000000000]) (some (5, 5, 3)) (some
    (5, 5, 3)) (.next ([5274000000000], [4140000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([1620000000000, 9000000000000], [1620000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1,
    3)) (.next ([1755000000000, -9000000000000], [2160000000000, 9000000000000]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([1620000000000, -9000000000000], [2370000000000, 9000000000000]) (some
    (5, 1, 3)) (some (5, 1, 3)) (.next ([3654000000000, -9000000000000], [5760000000000,
    9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2034000000000], [3390000000000])
    (some (5, 1, 3)) (some (5, 1, 3)) (.next ([75000000000], [135000000000]) (some (5, 1, 3)) (some
    (5, 1, 3)) (.next ([1899000000000], [3600000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([870000000000, 9000000000000], [2370000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1,
    3)) (.next ([0, 0], [1620000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([-540000000000], [3915000000000]) (some (5, 1, 3)) (some (5, 2, 3)) (.next ([-750000000000],
    [3990000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-2520000000000, 9000000000000],
    [7794000000000, -9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-4140000000000],
    [9414000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-1620000000000, -9000000000000],
    [3240000000000, 18000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-2160000000000,
    -9000000000000], [3915000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-2370000000000,
    -9000000000000], [3990000000000]) (some (5, 2, 3)) (some (5, 2, 4)) (.next ([-5760000000000,
    -9000000000000], [9414000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-3390000000000],
    [5424000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-135000000000], [210000000000])
    (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-3600000000000], [5499000000000]) (some (5, 2, 4))
    (some (5, 2, 4)) (.next ([-2370000000000, 9000000000000], [3240000000000]) (some (5, 2, 4))
    (some (5, 2, 5)) (.terminal (some (5, 2, 5)) (some (5, 2, 5)) (some (5, 2,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner5Part0 : FanWitness := (.next ([4836000000000], [24000000000]) (some (3, 1, 5)) (some
    (4, 1, 5)) (.next ([1110000000000], [15000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([4860000000000], [414000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([5265000000000, 0],
    [495000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([3735000000000],
    [1125000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([5250000000000, 0], [1620000000000,
    9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([2115000000000, -9000000000000],
    [1125000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([3240000000000, -9000000000000],
    [2034000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([4140000000000],
    [3735000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([4125000000000], [4860000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([1125000000000], [4140000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([0], [5250000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-9000000000], [3735000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-24000000000],
    [4860000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-15000000000], [1125000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-414000000000], [5274000000000]) (some (0, 2, 3))
    (some (0, 2, 3)) (.next ([-495000000000, -9000000000000], [5760000000000, 9000000000000]) (some
    (0, 2, 3)) (some (0, 2, 3)) (.next ([-1125000000000], [4860000000000]) (some (0, 2, 3)) (some
    (0, 2, 3)) (.next ([-1620000000000, -9000000000000], [6870000000000, 9000000000000]) (some (0,
    2, 3)) (some (0, 2, 3)) (.next ([-1125000000000, 0], [3240000000000, -9000000000000]) (some (0,
    2, 3)) (some (0, 2, 3)) (.next ([-2034000000000, -9000000000000], [5274000000000]) (some (0, 2,
    3)) (some (0, 5, 3)) (.next ([-3735000000000], [7875000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([-4860000000000], [8985000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-4140000000000], [5265000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5,
    3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner9Part0 : FanWitness := (.next ([4110000000000], [975000000000]) (some (5, 1, 2)) (some
    (5, 1, 2)) (.next ([240000000000], [135000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([2385000000000], [1905000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2145000000000],
    [1770000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2610000000000], [2655000000000])
    (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2370000000000], [2520000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([4860000000000], [5265000000000]) (some (5, 1, 2)) (some (5, 1, 2))
    (.next ([2340000000000], [4890000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([2205000000000], [5265000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([225000000000],
    [750000000000]) (some (5, 1, 2)) (some (5, 1, 5)) (.next ([750000000000], [4290000000000]) (some
    (5, 1, 5)) (some (5, 1, 5)) (.next ([0], [5265000000000]) (some (5, 1, 5)) (some (5, 1, 5))
    (.next ([-375000000000], [2895000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-975000000000], [5085000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-135000000000],
    [375000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1905000000000], [4290000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1770000000000], [3915000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-2655000000000], [5265000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-2520000000000], [4890000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-5265000000000], [10125000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4890000000000],
    [7230000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5265000000000], [7470000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-750000000000], [975000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-4290000000000], [5040000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.terminal (some (0, 1, 5)) (some (0, 1, 5)) (some (0, 1, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan38Owner5Part0 : FanWitness := (.next ([4836000000000], [24000000000]) (some (3, 1, 5)) (some
    (4, 1, 5)) (.next ([1110000000000], [15000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([4860000000000], [414000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([5265000000000, 0],
    [495000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([2130000000000,
    -9000000000000], [390000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([5250000000000, 0],
    [1620000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([4875000000000],
    [3015000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([3240000000000, -9000000000000],
    [2034000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([4860000000000],
    [4140000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([1125000000000], [4140000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([720000000000], [4164000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([0], [5250000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-9000000000], [3735000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-24000000000],
    [4860000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-15000000000], [1125000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-414000000000], [5274000000000]) (some (0, 2, 3))
    (some (0, 2, 3)) (.next ([-495000000000, -9000000000000], [5760000000000, 9000000000000]) (some
    (0, 2, 3)) (some (0, 2, 3)) (.next ([-390000000000, 0], [2520000000000, -9000000000000]) (some
    (0, 2, 3)) (some (0, 2, 3)) (.next ([-1620000000000, -9000000000000], [6870000000000,
    9000000000000]) (some (0, 2, 3)) (some (0, 5, 3)) (.next ([-3015000000000], [7890000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2034000000000, -9000000000000], [5274000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4140000000000], [9000000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-4140000000000], [5265000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-4164000000000], [4884000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some
    (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan38Owner9Part0 : FanWitness := (.next ([2385000000000], [1905000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([2145000000000], [1770000000000]) (some (5, 1, 2)) (some (5, 1, 2))
    (.next ([2610000000000], [2655000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([2370000000000], [2520000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([4140000000000],
    [5250000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1620000000000], [4875000000000])
    (some (5, 1, 2)) (some (5, 1, 2)) (.next ([225000000000], [750000000000]) (some (5, 1, 2)) (some
    (5, 1, 2)) (.next ([1485000000000], [5250000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([750000000000], [4290000000000]) (some (5, 1, 2)) (some (5, 1, 5)) (.next ([15000000000],
    [4125000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([0], [5265000000000]) (some (0, 1,
    5)) (some (0, 1, 5)) (.next ([-375000000000], [2895000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-960000000000], [4350000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-135000000000], [375000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1905000000000],
    [4290000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1770000000000], [3915000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2655000000000], [5265000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-2520000000000], [4890000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-5250000000000], [9390000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-4875000000000], [6495000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-750000000000],
    [975000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5250000000000], [6735000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4290000000000], [5040000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-4125000000000], [4140000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.terminal (some (0, 1, 5)) (some (0, 1, 5)) (some (0, 1, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan39Owner5Part0 : FanWitness := (.next ([4860000000000], [414000000000]) (some (0, 1, 5)) (some
    (0, 1, 5)) (.next ([5265000000000, 0], [495000000000, 9000000000000]) (some (0, 1, 5)) (some (0,
    1, 5)) (.next ([5250000000000, 0], [1620000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1,
    5)) (.next ([3240000000000, -9000000000000], [2034000000000, 9000000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([3750000000000], [4710000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([2130000000000, -9000000000000], [4710000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([1125000000000], [4140000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([564000000000], [3600000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([555000000000],
    [7335000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([540000000000], [8460000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0], [5250000000000]) (some (0, 1, 5)) (some (0, 1,
    5)) (.next ([-9000000000], [3735000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
    ([-24000000000], [4860000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-15000000000],
    [1125000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-414000000000], [5274000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-495000000000, -9000000000000], [5760000000000,
    9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1620000000000, -9000000000000],
    [6870000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2034000000000,
    -9000000000000], [5274000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4710000000000],
    [8460000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4710000000000, 0], [6840000000000,
    -9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4140000000000], [5265000000000])
    (some (0, 2, 5)) (some (0, 5, 5)) (.next ([-3600000000000], [4164000000000]) (some (0, 5, 5))
    (some (0, 5, 5)) (.next ([-7335000000000], [7890000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-8460000000000], [9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some
    (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_1 : ExcludedOn (model32.B 1 ++ [step32.q]) 9000000000000 (model32.caps 1)
    (model32.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_2 : ExcludedOn (model32.B 2 ++ [step32.q]) 9000000000000 (model32.caps 2)
    (model32.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_3 : ExcludedOn (model32.B 3 ++ [step32.q]) 9000000000000 (model32.caps 3)
    (model32.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000], [540000000000]) (some (4, 5, 2))
      (some (4, 5, 3)) (.next ([3240000000000], [750000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([4725000000000, -9000000000000], [1620000000000, 9000000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([5805000000000], [3915000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([5595000000000], [3990000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([1620000000000, 9000000000000], [1620000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5,
      3)) (.next ([1755000000000, -9000000000000], [2160000000000, 9000000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([1620000000000, -9000000000000], [2370000000000, 9000000000000])
      (some (4, 5, 3)) (some (4, 5, 3)) (.next ([75000000000], [135000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([1080000000000, 9000000000000], [2295000000000, -9000000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([870000000000, 9000000000000], [2370000000000,
      -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0, 0], [1620000000000,
      9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-540000000000], [3915000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-750000000000], [3990000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-1620000000000, -9000000000000], [6345000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-3915000000000], [9720000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-3990000000000], [9585000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-1620000000000, -9000000000000], [3240000000000, 18000000000000]) (some (0, 5, 3)) (some (5,
      5, 3)) (.next ([-2160000000000, -9000000000000], [3915000000000]) (some (5, 5, 3)) (some (5,
      5, 3)) (.next ([-2370000000000, -9000000000000], [3990000000000]) (some (5, 5, 3)) (some (5,
      5, 4)) (.next ([-135000000000], [210000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next
      ([-2295000000000, 9000000000000], [3375000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next
      ([-2370000000000, 9000000000000], [3240000000000]) (some (5, 5, 4)) (some (5, 5, 4))
      (.terminal (some (5, 5, 4)) (some (5, 2, 4)) (some (5, 5, 4))))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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

theorem checked32 : StepValid model32 9000000000000 step32 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded32_0
    · exact excluded32_1
    · exact excluded32_2
    · exact excluded32_3
    · exact excluded32_4
    · exact excluded32_5
    · exact excluded32_6
    · exact excluded32_7
    · exact excluded32_8
    · exact (hj rfl).elim
theorem next32 : model32.insert step32 = model33 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded33_0 : ExcludedOn (model33.B 0 ++ [step33.q]) 9000000000000 (model33.caps 0)
    (model33.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6855000000000], [165000000000]) (some (7, 8, 5))
      (some (7, 8, 5)) (.next ([6195000000000], [345000000000]) (some (7, 8, 5)) (some (7, 8, 5))
      (.next ([6105000000000], [540000000000]) (some (7, 8, 5)) (some (7, 8, 6))
      fan33Owner0Part1))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_1 : ExcludedOn (model33.B 1 ++ [step33.q]) 9000000000000 (model33.caps 1)
    (model33.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_2 : ExcludedOn (model33.B 2 ++ [step33.q]) 9000000000000 (model33.caps 2)
    (model33.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_3 : ExcludedOn (model33.B 3 ++ [step33.q]) 9000000000000 (model33.caps 3)
    (model33.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_5 : ExcludedOn (model33.B 5 ++ [step33.q]) 9000000000000 (model33.caps 5)
    (model33.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1110000000000], [15000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) fan33Owner5Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded34_1 : ExcludedOn (model34.B 1 ++ [step34.q]) 9000000000000 (model34.caps 1)
    (model34.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000, -9000000000000], [0,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([7380000000000, -9000000000000],
      [1620000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([3255000000000,
      -9000000000000], [5745000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([1620000000000], [4125000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0],
      [1620000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, -9000000000000],
      [4125000000000]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-1620000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (3, 1, 2)) (.next ([-5745000000000, 0],
      [9000000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-4125000000000],
      [5745000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_3 : ExcludedOn (model34.B 3 ++ [step34.q]) 9000000000000 (model34.caps 3)
    (model34.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([750000000000, -9000000000000], [0,
      9000000000000]) (some (3, 0, 5)) (some (4, 0, 5)) fan34Owner3Part0)) (den := 9000000000000)
      (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_4 : ExcludedOn (model34.B 4 ++ [step34.q]) 9000000000000 (model34.caps 4)
    (model34.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked34 : StepValid model34 9000000000000 step34 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded34_1
    · exact excluded34_2
    · exact excluded34_3
    · exact excluded34_4
    · exact excluded34_5
    · exact excluded34_6
    · exact excluded34_7
    · exact excluded34_8
    · exact excluded34_9
theorem next34 : model34.insert step34 = model35 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded35_0 : ExcludedOn (model35.B 0 ++ [step35.q]) 9000000000000 (model35.caps 0)
    (model35.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 7 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_1 : ExcludedOn (model35.B 1 ++ [step35.q]) 9000000000000 (model35.caps 1)
    (model35.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_2 : ExcludedOn (model35.B 2 ++ [step35.q]) 9000000000000 (model35.caps 2)
    (model35.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_3 : ExcludedOn (model35.B 3 ++ [step35.q]) 9000000000000 (model35.caps 3)
    (model35.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_4 : ExcludedOn (model35.B 4 ++ [step35.q]) 9000000000000 (model35.caps 4)
    (model35.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5559000000000], [201000000000]) (some (3, 0, 4))
      (some (3, 1, 4)) (.next ([4140000000000, -9000000000000], [1245000000000, 9000000000000])
      (some (3, 1, 4)) (some (3, 1, 4)) (.next ([5184000000000, 0], [1620000000000, 9000000000000])
      (some (3, 1, 4)) (some (3, 1, 4)) (.next ([3726000000000], [4860000000000]) (some (3, 1, 4))
      (some (3, 1, 4)) (.next ([2106000000000, -9000000000000], [4860000000000, 0]) (some (3, 1, 4))
      (some (3, 1, 4)) (.next ([525000000000], [2826000000000]) (some (3, 1, 4)) (some (3, 4, 4))
      (.next ([375000000000], [5385000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([324000000000], [8586000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0, 0],
      [1620000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-201000000000],
      [5760000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1245000000000, -9000000000000],
      [5385000000000, 0]) (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-1620000000000,
      -9000000000000], [6804000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-4860000000000], [8586000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-4860000000000,
      0], [6966000000000, -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-2826000000000], [3351000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-5385000000000], [5760000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-8586000000000], [8910000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4,
      3)) (some (0, 4, 3)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_6 : ExcludedOn (model35.B 6 ++ [step35.q]) 9000000000000 (model35.caps 6)
    (model35.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000], [540000000000]) (some (5, 5, 2))
      (some (5, 5, 3)) fan35Owner6Part0)) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100
      (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded35_1
    · exact excluded35_2
    · exact excluded35_3
    · exact excluded35_4
    · exact (hj rfl).elim
    · exact excluded35_6
    · exact excluded35_7
    · exact excluded35_8
    · exact excluded35_9
theorem next35 : model35.insert step35 = model36 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded36_0 : ExcludedOn (model36.B 0 ++ [step36.q]) 9000000000000 (model36.caps 0)
    (model36.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_1 : ExcludedOn (model36.B 1 ++ [step36.q]) 9000000000000 (model36.caps 1)
    (model36.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_2 : ExcludedOn (model36.B 2 ++ [step36.q]) 9000000000000 (model36.caps 2)
    (model36.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_3 : ExcludedOn (model36.B 3 ++ [step36.q]) 9000000000000 (model36.caps 3)
    (model36.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_4 : ExcludedOn (model36.B 4 ++ [step36.q]) 9000000000000 (model36.caps 4)
    (model36.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3726000000000], [9000000000]) (some (3, 0, 5))
      (some (3, 5, 5)) (.next ([4836000000000], [24000000000]) (some (3, 5, 5)) (some (4, 5, 5))
      (.next ([1110000000000], [15000000000]) (some (4, 5, 5)) (some (4, 5, 5)) (.next
      ([4860000000000], [414000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([5265000000000,
      0], [495000000000, 9000000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([5250000000000,
      0], [1620000000000, 9000000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([3240000000000,
      -9000000000000], [2034000000000, 9000000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next
      ([4860000000000], [4149000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([1620000000000,
      9000000000000], [2115000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([1125000000000], [4140000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([1125000000000],
      [7875000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0], [5250000000000]) (some (0, 5,
      3)) (some (0, 5, 3)) (.next ([-9000000000], [3735000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-24000000000], [4860000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-15000000000], [1125000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-414000000000],
      [5274000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-495000000000, -9000000000000],
      [5760000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1620000000000,
      -9000000000000], [6870000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-2034000000000, -9000000000000], [5274000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-4149000000000], [9009000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2115000000000,
      9000000000000], [3735000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4140000000000],
      [5265000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-7875000000000], [9000000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5,
      3))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded36_6 : ExcludedOn (model36.B 6 ++ [step36.q]) 9000000000000 (model36.caps 6)
    (model36.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_7 : ExcludedOn (model36.B 7 ++ [step36.q]) 9000000000000 (model36.caps 7)
    (model36.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_8 : ExcludedOn (model36.B 8 ++ [step36.q]) 9000000000000 (model36.caps 8)
    (model36.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded36_8
    · exact (hj rfl).elim
theorem next36 : model36.insert step36 = model37 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded37_0 : ExcludedOn (model37.B 0 ++ [step37.q]) 9000000000000 (model37.caps 0)
    (model37.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_1 : ExcludedOn (model37.B 1 ++ [step37.q]) 9000000000000 (model37.caps 1)
    (model37.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_2 : ExcludedOn (model37.B 2 ++ [step37.q]) 9000000000000 (model37.caps 2)
    (model37.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_3 : ExcludedOn (model37.B 3 ++ [step37.q]) 9000000000000 (model37.caps 3)
    (model37.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_4 : ExcludedOn (model37.B 4 ++ [step37.q]) 9000000000000 (model37.caps 4)
    (model37.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_5 : ExcludedOn (model37.B 5 ++ [step37.q]) 9000000000000 (model37.caps 5)
    (model37.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3726000000000], [9000000000]) (some (3, 0, 5))
      (some (3, 1, 5)) fan37Owner5Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_7 : ExcludedOn (model37.B 7 ++ [step37.q]) 9000000000000 (model37.caps 7)
    (model37.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_8 : ExcludedOn (model37.B 8 ++ [step37.q]) 9000000000000 (model37.caps 8)
    (model37.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_9 : ExcludedOn (model37.B 9 ++ [step37.q]) 9000000000000 (model37.caps 9)
    (model37.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2520000000000], [375000000000]) (some (5, 0, 1))
      (some (5, 1, 2)) fan37Owner9Part0)) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100
      (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded37_7
    · exact excluded37_8
    · exact excluded37_9
theorem next37 : model37.insert step37 = model38 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded38_0 : ExcludedOn (model38.B 0 ++ [step38.q]) 9000000000000 (model38.caps 0)
    (model38.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_1 : ExcludedOn (model38.B 1 ++ [step38.q]) 9000000000000 (model38.caps 1)
    (model38.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_2 : ExcludedOn (model38.B 2 ++ [step38.q]) 9000000000000 (model38.caps 2)
    (model38.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_3 : ExcludedOn (model38.B 3 ++ [step38.q]) 9000000000000 (model38.caps 3)
    (model38.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_4 : ExcludedOn (model38.B 4 ++ [step38.q]) 9000000000000 (model38.caps 4)
    (model38.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_5 : ExcludedOn (model38.B 5 ++ [step38.q]) 9000000000000 (model38.caps 5)
    (model38.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3726000000000], [9000000000]) (some (3, 0, 5))
      (some (3, 1, 5)) fan38Owner5Part0)) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded38_7 : ExcludedOn (model38.B 7 ++ [step38.q]) 9000000000000 (model38.caps 7)
    (model38.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_8 : ExcludedOn (model38.B 8 ++ [step38.q]) 9000000000000 (model38.caps 8)
    (model38.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_9 : ExcludedOn (model38.B 9 ++ [step38.q]) 9000000000000 (model38.caps 9)
    (model38.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2520000000000], [375000000000]) (some (5, 0, 1))
      (some (5, 1, 2)) (.next ([3390000000000], [960000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([240000000000], [135000000000]) (some (5, 1, 2)) (some (5, 1, 2)) fan38Owner9Part0))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded38_3
    · exact excluded38_4
    · exact excluded38_5
    · exact (hj rfl).elim
    · exact excluded38_7
    · exact excluded38_8
    · exact excluded38_9
theorem next38 : model38.insert step38 = model39 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded39_0 : ExcludedOn (model39.B 0 ++ [step39.q]) 9000000000000 (model39.caps 0)
    (model39.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 7 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_1 : ExcludedOn (model39.B 1 ++ [step39.q]) 9000000000000 (model39.caps 1)
    (model39.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5250000000000], [2670000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([5250000000000], [4290000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([1620000000000, 9000000000000], [1620000000000, 9000000000000]) (some
      (0, 3, 2)) (some (0, 3, 2)) (.next ([3630000000000, -9000000000000], [5910000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [1620000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-2670000000000, 9000000000000],
      [7920000000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-4290000000000],
      [9540000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1620000000000, -9000000000000],
      [3240000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-5910000000000,
      -9000000000000], [9540000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
      0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded39_2 : ExcludedOn (model39.B 2 ++ [step39.q]) 9000000000000 (model39.caps 2)
    (model39.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_3 : ExcludedOn (model39.B 3 ++ [step39.q]) 9000000000000 (model39.caps 3)
    (model39.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_4 : ExcludedOn (model39.B 4 ++ [step39.q]) 9000000000000 (model39.caps 4)
    (model39.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_5 : ExcludedOn (model39.B 5 ++ [step39.q]) 9000000000000 (model39.caps 5)
    (model39.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3726000000000], [9000000000]) (some (3, 0, 5))
      (some (3, 1, 5)) (.next ([4836000000000], [24000000000]) (some (3, 1, 5)) (some (4, 1, 5))
      (.next ([1110000000000], [15000000000]) (some (4, 1, 5)) (some (4, 1, 5)) fan39Owner5Part0))))
      (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded39_7 : ExcludedOn (model39.B 7 ++ [step39.q]) 9000000000000 (model39.caps 7)
    (model39.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_8 : ExcludedOn (model39.B 8 ++ [step39.q]) 9000000000000 (model39.caps 8)
    (model39.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_9 : ExcludedOn (model39.B 9 ++ [step39.q]) 9000000000000 (model39.caps 9)
    (model39.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded39_3
    · exact excluded39_4
    · exact excluded39_5
    · exact (hj rfl).elim
    · exact excluded39_7
    · exact excluded39_8
    · exact excluded39_9
theorem next39 : model39.insert step39 = model40 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint180000190000
end ConwaySoifer.Simplified.Certificates
