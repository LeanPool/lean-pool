/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint270000280000
import Mathlib.Tactic.FinCases

/-!
# Sint 270000 280000 6

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
namespace Sint270000280000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner0Part0 : FanWitness := (.next ([-5175000000000], [8010000000000]) (some (11, 4, 9))
    (some (11, 4, 9)) (.next ([-5250000000000], [7905000000000]) (some (11, 4, 9)) (some (11, 4, 9))
    (.next ([-60000000000], [90000000000]) (some (11, 4, 9)) (some (11, 4, 9)) (.next
    ([-5385000000000], [7695000000000]) (some (11, 4, 9)) (some (11, 5, 9)) (.next
    ([-5355000000000], [7560000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next ([-450000000000],
    [630000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next ([-2310000000000], [3120000000000])
    (some (11, 5, 9)) (some (11, 5, 9)) (.next ([-2400000000000], [3150000000000]) (some (11, 5, 9))
    (some (11, 5, 9)) (.next ([-345000000000], [450000000000]) (some (11, 5, 9)) (some (11, 5, 9))
    (.next ([-6315000000000], [7785000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-6390000000000], [7680000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-2685000000000], [3150000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-6525000000000], [7470000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-6495000000000], [7335000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next ([-345000000000],
    [375000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next ([-960000000000], [1035000000000])
    (some (11, 5, 9)) (some (11, 5, 9)) (.next ([-6390000000000], [6825000000000]) (some (11, 5, 9))
    (some (11, 5, 9)) (.next ([-1245000000000], [1320000000000]) (some (11, 5, 9)) (some (11, 5, 9))
    (.next ([-6465000000000], [6720000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-8505000000000], [8775000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-6390000000000], [6540000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-8400000000000], [8595000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-8055000000000], [8145000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-8190000000000], [8250000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.terminal (some (11, 5,
    9)) (some (11, 5, 11)) (some (11, 5, 11)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner0Part1 : FanWitness := (.next ([-840000000000], [5850000000000]) (some (11, 3, 7))
    (some (11, 3, 7)) (.next ([-915000000000], [6165000000000]) (some (11, 3, 7)) (some (11, 3, 7))
    (.next ([-945000000000], [6105000000000]) (some (11, 3, 7)) (some (11, 3, 7)) (.next
    ([-330000000000], [2085000000000]) (some (11, 3, 7)) (some (11, 3, 7)) (.next ([-945000000000],
    [5820000000000]) (some (11, 3, 7)) (some (11, 3, 7)) (.next ([-225000000000], [1365000000000])
    (some (11, 3, 7)) (some (11, 3, 7)) (.next ([-390000000000], [2175000000000]) (some (11, 3, 7))
    (some (11, 3, 7)) (.next ([-1680000000000], [8340000000000]) (some (11, 3, 7)) (some (11, 3, 7))
    (.next ([-30000000000], [135000000000]) (some (11, 3, 7)) (some (11, 3, 7)) (.next
    ([-1965000000000], [8625000000000]) (some (11, 3, 7)) (some (11, 3, 7)) (.next ([-675000000000],
    [2460000000000]) (some (11, 3, 7)) (some (11, 3, 7)) (.next ([-2805000000000], [9060000000000])
    (some (11, 3, 7)) (some (11, 3, 7)) (.next ([-2895000000000], [9090000000000]) (some (11, 3, 7))
    (some (11, 3, 7)) (.next ([-3180000000000], [9090000000000]) (some (11, 3, 7)) (some (11, 3, 7))
    (.next ([-405000000000], [1125000000000]) (some (11, 3, 7)) (some (11, 3, 7)) (.next
    ([-465000000000], [1215000000000]) (some (11, 3, 7)) (some (11, 3, 7)) (.next ([-405000000000],
    [840000000000]) (some (11, 3, 7)) (some (11, 3, 7)) (.next ([-1185000000000], [2400000000000])
    (some (11, 3, 7)) (some (11, 4, 7)) (.next ([-750000000000], [1500000000000]) (some (11, 4, 7))
    (some (11, 4, 7)) (.next ([-1470000000000], [2685000000000]) (some (11, 4, 7)) (some (11, 4, 7))
    (.next ([-105000000000], [180000000000]) (some (11, 4, 7)) (some (11, 4, 7)) (.next
    ([-315000000000], [525000000000]) (some (11, 4, 7)) (some (11, 4, 8)) (.next ([-210000000000],
    [345000000000]) (some (11, 4, 8)) (some (11, 4, 8)) (.next ([-750000000000], [1215000000000])
    (some (11, 4, 8)) (some (11, 4, 9)) fan48Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner0Part2 : FanWitness := (.next ([435000000000], [6390000000000]) (some (11, 1, 7))
    (some (11, 2, 7)) (.next ([75000000000], [1245000000000]) (some (11, 2, 7)) (some (11, 2, 7))
    (.next ([255000000000], [6465000000000]) (some (11, 2, 7)) (some (11, 2, 7)) (.next
    ([270000000000], [8505000000000]) (some (11, 2, 7)) (some (11, 2, 7)) (.next ([150000000000],
    [6390000000000]) (some (11, 2, 7)) (some (11, 2, 7)) (.next ([195000000000], [8400000000000])
    (some (11, 2, 7)) (some (11, 2, 7)) (.next ([90000000000], [8055000000000]) (some (11, 2, 7))
    (some (11, 2, 7)) (.next ([60000000000], [8190000000000]) (some (11, 2, 7)) (some (11, 2, 7))
    (.next ([0], [285000000000]) (some (11, 2, 7)) (some (11, 2, 7)) (.next ([-30000000000],
    [6465000000000]) (some (11, 2, 7)) (some (11, 3, 7)) (.next ([-90000000000], [6600000000000])
    (some (11, 3, 7)) (some (11, 3, 7)) (.next ([-195000000000], [6570000000000]) (some (11, 3, 7))
    (some (11, 3, 7)) (.next ([-285000000000], [5985000000000]) (some (11, 3, 7)) (some (11, 3, 7))
    (.next ([-315000000000], [5925000000000]) (some (11, 3, 7)) (some (11, 3, 7)) (.next
    ([-315000000000], [5640000000000]) (some (11, 3, 7)) (some (11, 3, 7)) (.next ([-375000000000],
    [6600000000000]) (some (11, 3, 7)) (some (11, 3, 7)) (.next ([-480000000000], [6570000000000])
    (some (11, 3, 7)) (some (11, 3, 7)) (.next ([-465000000000], [6060000000000]) (some (11, 3, 7))
    (some (11, 3, 7)) (.next ([-495000000000], [6000000000000]) (some (11, 3, 7)) (some (11, 3, 7))
    (.next ([-495000000000], [5940000000000]) (some (11, 3, 7)) (some (11, 3, 7)) (.next
    ([-495000000000], [5715000000000]) (some (11, 3, 7)) (some (11, 3, 7)) (.next ([-720000000000],
    [7305000000000]) (some (11, 3, 7)) (some (11, 3, 7)) (.next ([-810000000000], [6195000000000])
    (some (11, 3, 7)) (some (11, 3, 7)) (.next ([-840000000000], [6135000000000]) (some (11, 3, 7))
    (some (11, 3, 7)) fan48Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner0Part3 : FanWitness := (.next ([435000000000], [405000000000]) (some (11, 1, 7)) (some
    (11, 1, 7)) (.next ([1215000000000], [1185000000000]) (some (11, 1, 7)) (some (11, 1, 7)) (.next
    ([750000000000], [750000000000]) (some (11, 1, 7)) (some (11, 1, 7)) (.next ([1215000000000],
    [1470000000000]) (some (11, 1, 7)) (some (11, 1, 7)) (.next ([75000000000], [105000000000])
    (some (11, 1, 7)) (some (11, 1, 7)) (.next ([210000000000], [315000000000]) (some (11, 1, 7))
    (some (11, 1, 7)) (.next ([135000000000], [210000000000]) (some (11, 1, 7)) (some (11, 1, 7))
    (.next ([465000000000], [750000000000]) (some (11, 1, 7)) (some (11, 1, 7)) (.next
    ([2835000000000], [5175000000000]) (some (11, 1, 7)) (some (11, 1, 7)) (.next ([2655000000000],
    [5250000000000]) (some (11, 1, 7)) (some (11, 1, 7)) (.next ([30000000000], [60000000000]) (some
    (11, 1, 7)) (some (11, 1, 7)) (.next ([2310000000000], [5385000000000]) (some (11, 1, 7)) (some
    (11, 1, 7)) (.next ([2205000000000], [5355000000000]) (some (11, 1, 7)) (some (11, 1, 7)) (.next
    ([180000000000], [450000000000]) (some (11, 1, 7)) (some (11, 1, 7)) (.next ([810000000000],
    [2310000000000]) (some (11, 1, 7)) (some (11, 1, 7)) (.next ([750000000000], [2400000000000])
    (some (11, 1, 7)) (some (11, 1, 7)) (.next ([105000000000], [345000000000]) (some (11, 1, 7))
    (some (11, 1, 7)) (.next ([1470000000000], [6315000000000]) (some (11, 1, 7)) (some (11, 1, 7))
    (.next ([1290000000000], [6390000000000]) (some (11, 1, 7)) (some (11, 1, 7)) (.next
    ([465000000000], [2685000000000]) (some (11, 1, 7)) (some (11, 1, 7)) (.next ([945000000000],
    [6525000000000]) (some (11, 1, 7)) (some (11, 1, 7)) (.next ([840000000000], [6495000000000])
    (some (11, 1, 7)) (some (11, 1, 7)) (.next ([30000000000], [345000000000]) (some (11, 1, 7))
    (some (11, 1, 7)) (.next ([75000000000], [960000000000]) (some (11, 1, 7)) (some (11, 1, 7))
    fan48Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner0Part4 : FanWitness := (.next ([6090000000000], [480000000000]) (some (11, 11, 7))
    (some (11, 11, 7)) (.next ([5595000000000], [465000000000]) (some (11, 11, 7)) (some (11, 11,
    7)) (.next ([5505000000000], [495000000000]) (some (11, 11, 7)) (some (11, 11, 7)) (.next
    ([5445000000000], [495000000000]) (some (11, 11, 7)) (some (11, 11, 7)) (.next ([5220000000000],
    [495000000000]) (some (11, 0, 7)) (some (11, 0, 7)) (.next ([6585000000000], [720000000000])
    (some (11, 0, 7)) (some (11, 0, 7)) (.next ([5385000000000], [810000000000]) (some (11, 0, 7))
    (some (11, 0, 7)) (.next ([5295000000000], [840000000000]) (some (11, 0, 7)) (some (11, 0, 7))
    (.next ([5010000000000], [840000000000]) (some (11, 0, 7)) (some (11, 0, 7)) (.next
    ([5250000000000], [915000000000]) (some (11, 0, 7)) (some (11, 0, 7)) (.next ([5160000000000],
    [945000000000]) (some (11, 0, 7)) (some (11, 0, 7)) (.next ([1755000000000], [330000000000])
    (some (11, 0, 7)) (some (11, 0, 7)) (.next ([4875000000000], [945000000000]) (some (11, 0, 7))
    (some (11, 0, 7)) (.next ([1140000000000], [225000000000]) (some (11, 0, 7)) (some (11, 0, 7))
    (.next ([1785000000000], [390000000000]) (some (11, 0, 7)) (some (11, 1, 7)) (.next
    ([6660000000000], [1680000000000]) (some (11, 1, 7)) (some (11, 1, 7)) (.next ([105000000000],
    [30000000000]) (some (11, 1, 7)) (some (11, 1, 7)) (.next ([6660000000000], [1965000000000])
    (some (11, 1, 7)) (some (11, 1, 7)) (.next ([1785000000000], [675000000000]) (some (11, 1, 7))
    (some (11, 1, 7)) (.next ([6255000000000], [2805000000000]) (some (11, 1, 7)) (some (11, 1, 7))
    (.next ([6195000000000], [2895000000000]) (some (11, 1, 7)) (some (11, 1, 7)) (.next
    ([5910000000000], [3180000000000]) (some (11, 1, 7)) (some (11, 1, 7)) (.next ([720000000000],
    [405000000000]) (some (11, 1, 7)) (some (11, 1, 7)) (.next ([750000000000], [465000000000])
    (some (11, 1, 7)) (some (11, 1, 7)) fan48Owner0Part3))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner4Part0 : FanWitness := (.next ([1125000000000], [5445000000000]) (some (5, 1, 4))
    (some (5, 1, 4)) (.next ([855000000000], [6555000000000]) (some (5, 1, 4)) (some (5, 1, 4))
    (.next ([570000000000], [6660000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next
    ([120000000000], [7125000000000]) (some (5, 1, 4)) (some (5, 1, 6)) (.next ([0, 0],
    [2430000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, -9000000000000],
    [4125000000000, 0]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-165000000000, -9000000000000],
    [4860000000000, 0]) (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-645000000000, -9000000000000],
    [6000000000000, 0]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1020000000000], [7785000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1305000000000, -9000000000000], [7875000000000,
    9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-165000000000], [735000000000]) (some
    (0, 2, 6)) (some (0, 2, 6)) (.next ([-465000000000], [1590000000000]) (some (0, 2, 6)) (some (0,
    3, 6)) (.next ([-2430000000000, -9000000000000], [7410000000000, 9000000000000]) (some (0, 3,
    6)) (some (0, 3, 6)) (.next ([-645000000000], [1875000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([-480000000000], [1140000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-4125000000000], [6555000000000]) (some (0, 3, 6)) (some (0, 4, 6)) (.next ([-4860000000000],
    [7125000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-5430000000000], [7875000000000])
    (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-6000000000000], [7785000000000]) (some (0, 4, 6))
    (some (0, 4, 6)) (.next ([-6000000000000], [7710000000000]) (some (0, 4, 6)) (some (0, 4, 6))
    (.next ([-5445000000000], [6570000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next
    ([-6555000000000], [7410000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-6660000000000],
    [7230000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-7125000000000], [7245000000000])
    (some (0, 4, 6)) (some (0, 4, 6)) (.terminal (some (0, 4, 6)) (some (0, 4, 6)) (some (0, 4,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan49Owner3Part0 : FanWitness := (.next ([1125000000000, -9000000000000], [0, 9000000000000])
    (some (4, 0, 2)) (some (4, 5, 2)) (.next ([6165000000000], [930000000000]) (some (4, 5, 2))
    (some (4, 5, 2)) (.next ([5595000000000], [1500000000000]) (some (4, 5, 2)) (some (4, 5, 2))
    (.next ([2430000000000], [1125000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
    ([5190000000000], [2430000000000, 9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
    ([2430000000000], [1695000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([4065000000000],
    [3555000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([3495000000000], [4125000000000])
    (some (4, 5, 2)) (some (4, 5, 2)) (.next ([2625000000000], [4665000000000]) (some (4, 5, 2))
    (some (4, 5, 2)) (.next ([525000000000], [2100000000000]) (some (4, 5, 2)) (some (4, 5, 2))
    (.next ([195000000000, -9000000000000], [7095000000000, 9000000000000]) (some (4, 5, 2)) (some
    (4, 5, 3)) (.next ([0], [2430000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([0, -9000000000000], [1695000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0,
    -9000000000000], [1125000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-930000000000],
    [7095000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1500000000000], [7095000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1125000000000], [3555000000000]) (some (0, 2, 3))
    (some (0, 2, 3)) (.next ([-2430000000000, -9000000000000], [7620000000000, 9000000000000]) (some
    (0, 2, 3)) (some (0, 2, 3)) (.next ([-1695000000000], [4125000000000]) (some (0, 2, 3)) (some
    (0, 2, 3)) (.next ([-3555000000000], [7620000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([-4125000000000], [7620000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-4665000000000],
    [7290000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2100000000000], [2625000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-7095000000000, -9000000000000], [7290000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2, 3)) (some (0, 2, 3)) (some (0, 2,
    3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan49Owner4Part0 : FanWitness := (.next ([855000000000], [6555000000000]) (some (5, 1, 4)) (some
    (5, 1, 4)) (.next ([570000000000], [6090000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next
    ([105000000000], [1590000000000]) (some (5, 1, 4)) (some (5, 1, 6)) (.next ([120000000000],
    [7125000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, 0], [2430000000000,
    9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, -9000000000000], [4125000000000,
    0]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-165000000000, -9000000000000], [4860000000000,
    0]) (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-735000000000, -9000000000000], [7305000000000,
    9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-645000000000, -9000000000000],
    [6000000000000, 0]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1020000000000], [7785000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-165000000000], [735000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-2430000000000, -9000000000000], [7410000000000, 9000000000000]) (some
    (0, 2, 6)) (some (0, 3, 6)) (.next ([-645000000000], [1875000000000]) (some (0, 3, 6)) (some (0,
    3, 6)) (.next ([-480000000000], [1140000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-4125000000000], [6555000000000]) (some (0, 3, 6)) (some (0, 4, 6)) (.next ([-4860000000000],
    [7305000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-4860000000000], [7125000000000])
    (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-4875000000000], [6570000000000]) (some (0, 4, 6))
    (some (0, 4, 6)) (.next ([-5430000000000], [7140000000000]) (some (0, 4, 6)) (some (0, 4, 6))
    (.next ([-6000000000000], [7785000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next
    ([-6555000000000], [7410000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-6090000000000],
    [6660000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-1590000000000], [1695000000000])
    (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-7125000000000], [7245000000000]) (some (0, 4, 5))
    (some (0, 4, 5)) (.terminal (some (0, 4, 5)) (some (0, 4, 5)) (some (0, 4,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan50Owner4Part0 : FanWitness := (.next ([4980000000000], [4215000000000]) (some (5, 6, 4))
    (some (5, 6, 4)) (.next ([2430000000000], [4125000000000]) (some (5, 6, 4)) (some (5, 6, 4))
    (.next ([2265000000000], [4860000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
    ([1785000000000], [6000000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([855000000000],
    [6555000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([120000000000], [7125000000000])
    (some (5, 6, 4)) (some (5, 6, 4)) (.next ([0, 0], [2430000000000, 9000000000000]) (some (5, 6,
    4)) (some (5, 6, 4)) (.next ([0, -9000000000000], [4125000000000, 0]) (some (0, 6, 4)) (some (0,
    6, 4)) (.next ([-165000000000, -9000000000000], [4860000000000, 0]) (some (0, 6, 4)) (some (0,
    6, 4)) (.next ([-645000000000, -9000000000000], [6000000000000, 0]) (some (0, 6, 4)) (some (0,
    6, 4)) (.next ([-1020000000000], [7785000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-165000000000], [735000000000]) (some (0, 6, 4)) (some (0, 6, 5)) (.next ([-2430000000000,
    -9000000000000], [7410000000000, 9000000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-645000000000], [1875000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-1950000000000],
    [4860000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-2430000000000], [6000000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-480000000000], [1140000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([-1785000000000], [4125000000000]) (some (0, 3, 5)) (some (0, 4, 5))
    (.next ([-4215000000000], [9195000000000]) (some (0, 4, 5)) (some (0, 4, 5)) (.next
    ([-4125000000000], [6555000000000]) (some (0, 4, 5)) (some (0, 4, 5)) (.next ([-4860000000000],
    [7125000000000]) (some (0, 4, 5)) (some (0, 4, 5)) (.next ([-6000000000000], [7785000000000])
    (some (0, 4, 5)) (some (0, 4, 5)) (.next ([-6555000000000], [7410000000000]) (some (0, 4, 5))
    (some (0, 4, 5)) (.next ([-7125000000000], [7245000000000]) (some (0, 4, 5)) (some (0, 4, 5))
    (.terminal (some (0, 4, 5)) (some (0, 4, 5)) (some (0, 4, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan52Owner4Part0 : FanWitness := (.next ([345000000000], [1365000000000]) (some (5, 1, 6)) (some
    (5, 1, 6)) (.next ([900000000000], [6570000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
    ([855000000000], [6555000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([120000000000],
    [7125000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, 0], [2430000000000,
    9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, -9000000000000], [4125000000000,
    0]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-165000000000, -9000000000000], [4860000000000,
    0]) (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-645000000000, -9000000000000], [6000000000000,
    0]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1020000000000], [7785000000000]) (some (0, 2,
    6)) (some (0, 2, 6)) (.next ([-1590000000000], [7470000000000]) (some (0, 2, 6)) (some (0, 2,
    6)) (.next ([-165000000000], [735000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1530000000000, -9000000000000], [6570000000000, 0]) (some (0, 2, 5)) (some (0, 3, 5)) (.next
    ([-2430000000000, -9000000000000], [7410000000000, 9000000000000]) (some (0, 3, 5)) (some (0, 3,
    5)) (.next ([-645000000000], [1875000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([-315000000000], [885000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-480000000000],
    [1140000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-1530000000000], [2445000000000])
    (some (0, 3, 5)) (some (0, 4, 5)) (.next ([-4125000000000], [6555000000000]) (some (0, 4, 5))
    (some (0, 4, 5)) (.next ([-4860000000000], [7125000000000]) (some (0, 4, 5)) (some (0, 4, 5))
    (.next ([-6000000000000], [7785000000000]) (some (0, 4, 5)) (some (0, 4, 5)) (.next
    ([-1365000000000], [1710000000000]) (some (0, 4, 5)) (some (0, 4, 5)) (.next ([-6570000000000],
    [7470000000000]) (some (0, 4, 5)) (some (0, 4, 5)) (.next ([-6555000000000], [7410000000000])
    (some (0, 4, 5)) (some (0, 4, 5)) (.next ([-7125000000000], [7245000000000]) (some (0, 4, 5))
    (some (0, 4, 5)) (.terminal (some (0, 4, 5)) (some (0, 4, 5)) (some (0, 4,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan52Owner5Part0 : FanWitness := (.next ([6570000000000], [1530000000000]) (some (5, 1, 2))
    (some (5, 1, 3)) (.next ([4785000000000], [1695000000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([4785000000000, 0], [2430000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([4050000000000, -9000000000000], [2430000000000, 9000000000000]) (some (5, 1, 3)) (some
    (5, 1, 3)) (.next ([4140000000000, -9000000000000], [3960000000000, 9000000000000]) (some (5, 1,
    3)) (some (5, 1, 3)) (.next ([2250000000000], [2250000000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([3255000000000], [3315000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([1980000000000], [2250000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2535000000000],
    [4500000000000]) (some (0, 1, 3)) (some (0, 1, 4)) (.next ([2070000000000], [3780000000000])
    (some (0, 1, 4)) (some (0, 1, 4)) (.next ([90000000000], [1530000000000]) (some (0, 1, 4)) (some
    (0, 1, 4)) (.next ([0], [4785000000000]) (some (0, 1, 4)) (some (0, 1, 5)) (.next
    ([-180000000000, -9000000000000], [2250000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
    ([-1530000000000], [8100000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1695000000000],
    [6480000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2430000000000, -9000000000000],
    [7215000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2430000000000,
    -9000000000000], [6480000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3960000000000,
    -9000000000000], [8100000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2250000000000],
    [4500000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3315000000000], [6570000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2250000000000], [4230000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-4500000000000], [7035000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-3780000000000], [5850000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1530000000000], [1620000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2,
    5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

theorem excluded48_0 : ExcludedOn (model48.B 0 ++ [step48.q]) 9000000000000 (model48.caps 0)
    (model48.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6435000000000], [30000000000]) (some (11, 11,
      5)) (some (11, 11, 6)) (.next ([6510000000000], [90000000000]) (some (11, 11, 6)) (some (11,
      11, 6)) (.next ([6375000000000], [195000000000]) (some (11, 11, 6)) (some (11, 11, 6)) (.next
      ([5700000000000], [285000000000]) (some (11, 11, 6)) (some (11, 11, 6)) (.next
      ([5610000000000], [315000000000]) (some (11, 11, 6)) (some (11, 11, 6)) (.next
      ([5325000000000], [315000000000]) (some (11, 11, 6)) (some (11, 11, 6)) (.next
      ([6225000000000], [375000000000]) (some (11, 11, 6)) (some (11, 11, 7))
      fan48Owner0Part4))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded48_1 : ExcludedOn (model48.B 1 ++ [step48.q]) 9000000000000 (model48.caps 1)
    (model48.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_2 : ExcludedOn (model48.B 2 ++ [step48.q]) 9000000000000 (model48.caps 2)
    (model48.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_4 : ExcludedOn (model48.B 4 ++ [step48.q]) 9000000000000 (model48.caps 4)
    (model48.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000, -9000000000000], [0,
      9000000000000]) (some (6, 0, 4)) (some (6, 1, 4)) (.next ([4695000000000, -9000000000000],
      [165000000000, 9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([5355000000000,
      -9000000000000], [645000000000, 9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
      ([6765000000000], [1020000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([6570000000000,
      0], [1305000000000, 9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([570000000000],
      [165000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([1125000000000], [465000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([4980000000000, 0], [2430000000000, 9000000000000])
      (some (5, 1, 4)) (some (5, 1, 4)) (.next ([1230000000000], [645000000000]) (some (5, 1, 4))
      (some (5, 1, 4)) (.next ([660000000000], [480000000000]) (some (5, 1, 4)) (some (5, 1, 4))
      (.next ([2430000000000], [4125000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next
      ([2265000000000], [4860000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([2445000000000],
      [5430000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([1785000000000], [6000000000000])
      (some (5, 1, 4)) (some (5, 1, 4)) (.next ([1710000000000], [6000000000000]) (some (5, 1, 4))
      (some (5, 1, 4)) fan48Owner4Part0)))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded48_5 : ExcludedOn (model48.B 5 ++ [step48.q]) 9000000000000 (model48.caps 5)
    (model48.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_6 : ExcludedOn (model48.B 6 ++ [step48.q]) 9000000000000 (model48.caps 6)
    (model48.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_7 : ExcludedOn (model48.B 7 ++ [step48.q]) 9000000000000 (model48.caps 7)
    (model48.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_8 : ExcludedOn (model48.B 8 ++ [step48.q]) 9000000000000 (model48.caps 8)
    (model48.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8070000000000], [105000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([1500000000000], [2055000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([3555000000000], [6570000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([1950000000000], [4620000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [8175000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-105000000000], [8175000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2055000000000], [3555000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-6570000000000], [10125000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-4620000000000], [6570000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some
      (0, 1, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded48_9 : ExcludedOn (model48.B 9 ++ [step48.q]) 9000000000000 (model48.caps 9)
    (model48.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked48 : StepValid model48 9000000000000 step48 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded48_0
    · exact excluded48_1
    · exact excluded48_2
    · exact (hj rfl).elim
    · exact excluded48_4
    · exact excluded48_5
    · exact excluded48_6
    · exact excluded48_7
    · exact excluded48_8
    · exact excluded48_9
theorem next48 : model48.insert step48 = model49 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded49_1 : ExcludedOn (model49.B 1 ++ [step49.q]) 9000000000000 (model49.caps 1)
    (model49.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_2 : ExcludedOn (model49.B 2 ++ [step49.q]) 9000000000000 (model49.caps 2)
    (model49.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_3 : ExcludedOn (model49.B 3 ++ [step49.q]) 9000000000000 (model49.caps 3)
    (model49.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1695000000000, -9000000000000], [0,
      9000000000000]) (some (3, 0, 2)) (some (4, 0, 2)) fan49Owner3Part0)) (den := 9000000000000)
      (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded49_4 : ExcludedOn (model49.B 4 ++ [step49.q]) 9000000000000 (model49.caps 4)
    (model49.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000, -9000000000000], [0,
      9000000000000]) (some (5, 0, 4)) (some (5, 1, 4)) (.next ([4695000000000, -9000000000000],
      [165000000000, 9000000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([6570000000000, 0],
      [735000000000, 9000000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([5355000000000,
      -9000000000000], [645000000000, 9000000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next
      ([6765000000000], [1020000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([570000000000],
      [165000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([4980000000000, 0], [2430000000000,
      9000000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([1230000000000], [645000000000])
      (some (5, 1, 4)) (some (5, 1, 4)) (.next ([660000000000], [480000000000]) (some (5, 1, 4))
      (some (5, 1, 4)) (.next ([2430000000000], [4125000000000]) (some (5, 1, 4)) (some (5, 1, 4))
      (.next ([2445000000000], [4860000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next
      ([2265000000000], [4860000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([1695000000000],
      [4875000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([1710000000000], [5430000000000])
      (some (5, 1, 4)) (some (5, 1, 4)) (.next ([1785000000000], [6000000000000]) (some (5, 1, 4))
      (some (5, 1, 4)) fan49Owner4Part0)))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded49_5 : ExcludedOn (model49.B 5 ++ [step49.q]) 9000000000000 (model49.caps 5)
    (model49.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_6 : ExcludedOn (model49.B 6 ++ [step49.q]) 9000000000000 (model49.caps 6)
    (model49.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_7 : ExcludedOn (model49.B 7 ++ [step49.q]) 9000000000000 (model49.caps 7)
    (model49.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_8 : ExcludedOn (model49.B 8 ++ [step49.q]) 9000000000000 (model49.caps 8)
    (model49.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_9 : ExcludedOn (model49.B 9 ++ [step49.q]) 9000000000000 (model49.caps 9)
    (model49.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked49 : StepValid model49 9000000000000 step49 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded49_1
    · exact excluded49_2
    · exact excluded49_3
    · exact excluded49_4
    · exact excluded49_5
    · exact excluded49_6
    · exact excluded49_7
    · exact excluded49_8
    · exact excluded49_9
theorem next49 : model49.insert step49 = model50 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded50_0 : ExcludedOn (model50.B 0 ++ [step50.q]) 9000000000000 (model50.caps 0)
    (model50.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 8 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_1 : ExcludedOn (model50.B 1 ++ [step50.q]) 9000000000000 (model50.caps 1)
    (model50.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_2 : ExcludedOn (model50.B 2 ++ [step50.q]) 9000000000000 (model50.caps 2)
    (model50.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_3 : ExcludedOn (model50.B 3 ++ [step50.q]) 9000000000000 (model50.caps 3)
    (model50.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_4 : ExcludedOn (model50.B 4 ++ [step50.q]) 9000000000000 (model50.caps 4)
    (model50.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000, -9000000000000], [0,
      9000000000000]) (some (5, 0, 4)) (some (5, 6, 4)) (.next ([4695000000000, -9000000000000],
      [165000000000, 9000000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([5355000000000,
      -9000000000000], [645000000000, 9000000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
      ([6765000000000], [1020000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([570000000000],
      [165000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([4980000000000, 0], [2430000000000,
      9000000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([1230000000000], [645000000000])
      (some (5, 6, 4)) (some (5, 6, 4)) (.next ([2910000000000], [1950000000000]) (some (5, 6, 4))
      (some (5, 6, 4)) (.next ([3570000000000], [2430000000000]) (some (5, 6, 4)) (some (5, 6, 4))
      (.next ([660000000000], [480000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
      ([2340000000000], [1785000000000]) (some (5, 6, 4)) (some (5, 6, 4))
      fan50Owner4Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded50_6 : ExcludedOn (model50.B 6 ++ [step50.q]) 9000000000000 (model50.caps 6)
    (model50.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_7 : ExcludedOn (model50.B 7 ++ [step50.q]) 9000000000000 (model50.caps 7)
    (model50.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_8 : ExcludedOn (model50.B 8 ++ [step50.q]) 9000000000000 (model50.caps 8)
    (model50.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_9 : ExcludedOn (model50.B 9 ++ [step50.q]) 9000000000000 (model50.caps 9)
    (model50.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked50 : StepValid model50 9000000000000 step50 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded50_0
    · exact excluded50_1
    · exact excluded50_2
    · exact excluded50_3
    · exact excluded50_4
    · exact (hj rfl).elim
    · exact excluded50_6
    · exact excluded50_7
    · exact excluded50_8
    · exact excluded50_9
theorem next50 : model50.insert step50 = model51 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded51_0 : ExcludedOn (model51.B 0 ++ [step51.q]) 9000000000000 (model51.caps 0)
    (model51.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_1 : ExcludedOn (model51.B 1 ++ [step51.q]) 9000000000000 (model51.caps 1)
    (model51.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_3 : ExcludedOn (model51.B 3 ++ [step51.q]) 9000000000000 (model51.caps 3)
    (model51.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1125000000000, -9000000000000], [0,
      9000000000000]) (some (3, 0, 2)) (some (4, 0, 2)) (.next ([6165000000000], [930000000000])
      (some (4, 0, 2)) (some (4, 1, 2)) (.next ([6060000000000], [2430000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2430000000000], [1125000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([5190000000000], [2430000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([4935000000000], [3555000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([4065000000000], [3555000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([1395000000000], [1230000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2625000000000],
      [4665000000000]) (some (4, 1, 2)) (some (4, 1, 5)) (.next ([525000000000], [2100000000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([195000000000, -9000000000000], [7095000000000,
      9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0], [2430000000000, 9000000000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0, -9000000000000], [1125000000000]) (some (0, 1,
      5)) (some (0, 1, 5)) (.next ([-930000000000], [7095000000000]) (some (0, 1, 5)) (some (0, 1,
      5)) (.next ([-2430000000000, -9000000000000], [8490000000000, 9000000000000]) (some (0, 1, 5))
      (some (0, 2, 5)) (.next ([-1125000000000], [3555000000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-2430000000000, -9000000000000], [7620000000000, 9000000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([-3555000000000], [8490000000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-3555000000000], [7620000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-1230000000000], [2625000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-4665000000000], [7290000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-2100000000000], [2625000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-7095000000000,
      -9000000000000], [7290000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2,
      5)) (some (0, 2, 3)) (some (0, 2, 5))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded51_4 : ExcludedOn (model51.B 4 ++ [step51.q]) 9000000000000 (model51.caps 4)
    (model51.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_5 : ExcludedOn (model51.B 5 ++ [step51.q]) 9000000000000 (model51.caps 5)
    (model51.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_6 : ExcludedOn (model51.B 6 ++ [step51.q]) 9000000000000 (model51.caps 6)
    (model51.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_7 : ExcludedOn (model51.B 7 ++ [step51.q]) 9000000000000 (model51.caps 7)
    (model51.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_8 : ExcludedOn (model51.B 8 ++ [step51.q]) 9000000000000 (model51.caps 8)
    (model51.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_9 : ExcludedOn (model51.B 9 ++ [step51.q]) 9000000000000 (model51.caps 9)
    (model51.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked51 : StepValid model51 9000000000000 step51 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded51_0
    · exact excluded51_1
    · exact (hj rfl).elim
    · exact excluded51_3
    · exact excluded51_4
    · exact excluded51_5
    · exact excluded51_6
    · exact excluded51_7
    · exact excluded51_8
    · exact excluded51_9
theorem next51 : model51.insert step51 = model52 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded52_1 : ExcludedOn (model52.B 1 ++ [step52.q]) 9000000000000 (model52.caps 1)
    (model52.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_2 : ExcludedOn (model52.B 2 ++ [step52.q]) 9000000000000 (model52.caps 2)
    (model52.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_3 : ExcludedOn (model52.B 3 ++ [step52.q]) 9000000000000 (model52.caps 3)
    (model52.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7470000000000, -9000000000000], [0,
      9000000000000]) (some (3, 0, 5)) (some (4, 0, 5)) (.next ([7095000000000], [180000000000])
      (some (4, 0, 5)) (some (4, 5, 5)) (.next ([6165000000000], [930000000000]) (some (4, 5, 2))
      (some (4, 5, 2)) (.next ([7620000000000], [2280000000000]) (some (4, 5, 2)) (some (4, 5, 2))
      (.next ([2430000000000], [1125000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
      ([5190000000000], [2430000000000, 9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
      ([4065000000000], [3555000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([2625000000000],
      [4665000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([2430000000000], [7470000000000])
      (some (4, 5, 2)) (some (4, 5, 2)) (.next ([525000000000], [2100000000000]) (some (4, 5, 2))
      (some (4, 5, 2)) (.next ([195000000000, -9000000000000], [7095000000000, 9000000000000]) (some
      (4, 5, 2)) (some (4, 5, 3)) (.next ([0], [2430000000000, 9000000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([0, -9000000000000], [7470000000000]) (some (0, 5, 3)) (some (0, 5,
      3)) (.next ([-180000000000], [7275000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-930000000000], [7095000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2280000000000],
      [9900000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1125000000000], [3555000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2430000000000, -9000000000000], [7620000000000,
      9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3555000000000], [7620000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4665000000000], [7290000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-7470000000000], [9900000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-2100000000000], [2625000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-7095000000000, -9000000000000], [7290000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3))))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded52_4 : ExcludedOn (model52.B 4 ++ [step52.q]) 9000000000000 (model52.caps 4)
    (model52.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000, -9000000000000], [0,
      9000000000000]) (some (5, 0, 4)) (some (5, 1, 4)) (.next ([4695000000000, -9000000000000],
      [165000000000, 9000000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([5355000000000,
      -9000000000000], [645000000000, 9000000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next
      ([6765000000000], [1020000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([5880000000000],
      [1590000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([570000000000], [165000000000])
      (some (5, 1, 4)) (some (5, 1, 4)) (.next ([5040000000000, -9000000000000], [1530000000000,
      9000000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([4980000000000, 0], [2430000000000,
      9000000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([1230000000000], [645000000000])
      (some (5, 1, 4)) (some (5, 1, 4)) (.next ([570000000000], [315000000000]) (some (5, 1, 4))
      (some (5, 1, 4)) (.next ([660000000000], [480000000000]) (some (5, 1, 4)) (some (5, 1, 6))
      (.next ([915000000000], [1530000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([2430000000000], [4125000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2265000000000],
      [4860000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1785000000000], [6000000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) fan52Owner4Part0)))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded52_5 : ExcludedOn (model52.B 5 ++ [step52.q]) 9000000000000 (model52.caps 5)
    (model52.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2070000000000, -9000000000000], [180000000000,
      9000000000000]) (some (5, 0, 2)) (some (5, 1, 2)) fan52Owner5Part0)) (den := 9000000000000)
      (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded52_6 : ExcludedOn (model52.B 6 ++ [step52.q]) 9000000000000 (model52.caps 6)
    (model52.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_7 : ExcludedOn (model52.B 7 ++ [step52.q]) 9000000000000 (model52.caps 7)
    (model52.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_8 : ExcludedOn (model52.B 8 ++ [step52.q]) 9000000000000 (model52.caps 8)
    (model52.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_9 : ExcludedOn (model52.B 9 ++ [step52.q]) 9000000000000 (model52.caps 9)
    (model52.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked52 : StepValid model52 9000000000000 step52 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded52_1
    · exact excluded52_2
    · exact excluded52_3
    · exact excluded52_4
    · exact excluded52_5
    · exact excluded52_6
    · exact excluded52_7
    · exact excluded52_8
    · exact excluded52_9
theorem next52 : model52.insert step52 = model53 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded53_1 : ExcludedOn (model53.B 1 ++ [step53.q]) 9000000000000 (model53.caps 1)
    (model53.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4860000000000], [2625000000000]) none none
      (.next ([3765000000000, 0], [2430000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([2430000000000, -9000000000000], [2625000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([1140000000000], [7485000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [2430000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2625000000000],
      [7485000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2430000000000, -9000000000000],
      [6195000000000, 9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2625000000000, 0],
      [5055000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-7485000000000],
      [8625000000000]) (some (3, 1, 0)) none (.terminal none none none))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded53_2 : ExcludedOn (model53.B 2 ++ [step53.q]) 9000000000000 (model53.caps 2)
    (model53.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4140000000000], [315000000000]) (some (0, 0, 1))
      (some (0, 0, 1)) (.next ([6570000000000, -9000000000000], [2940000000000, 0]) (some (0, 0, 1))
      (some (0, 3, 1)) (.next ([2625000000000], [1515000000000]) (some (0, 3, 1)) (some (0, 3, 1))
      (.next ([2430000000000, -9000000000000], [2625000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1))
      (.next ([0], [2940000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-315000000000],
      [4455000000000]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-2940000000000, 0],
      [9510000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1515000000000],
      [4140000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2625000000000, 0],
      [5055000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2))
      (some (0, 1, 0)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded53_3 : ExcludedOn (model53.B 3 ++ [step53.q]) 9000000000000 (model53.caps 3)
    (model53.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_4 : ExcludedOn (model53.B 4 ++ [step53.q]) 9000000000000 (model53.caps 4)
    (model53.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_5 : ExcludedOn (model53.B 5 ++ [step53.q]) 9000000000000 (model53.caps 5)
    (model53.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_6 : ExcludedOn (model53.B 6 ++ [step53.q]) 9000000000000 (model53.caps 6)
    (model53.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_7 : ExcludedOn (model53.B 7 ++ [step53.q]) 9000000000000 (model53.caps 7)
    (model53.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_8 : ExcludedOn (model53.B 8 ++ [step53.q]) 9000000000000 (model53.caps 8)
    (model53.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_9 : ExcludedOn (model53.B 9 ++ [step53.q]) 9000000000000 (model53.caps 9)
    (model53.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked53 : StepValid model53 9000000000000 step53 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded53_1
    · exact excluded53_2
    · exact excluded53_3
    · exact excluded53_4
    · exact excluded53_5
    · exact excluded53_6
    · exact excluded53_7
    · exact excluded53_8
    · exact excluded53_9
theorem next53 : model53.insert step53 = model54 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint270000280000
end ConwaySoifer.Simplified.Certificates
