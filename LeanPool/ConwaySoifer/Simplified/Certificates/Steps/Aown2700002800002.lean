/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown270000280000
import Mathlib.Tactic.FinCases

/-!
# Aown 270000 280000 2

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
namespace Aown270000280000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan16Owner0Part0 : FanWitness := (.next ([-3596400000000, -4320000000000], [9208200000000,
    2160000000000]) (some (0, 6, 10)) (some (0, 6, 10)) (.next ([-601800000000, 2160000000000],
    [1393200000000, 2160000000000]) (some (0, 6, 10)) (some (0, 10, 10)) (.next ([-1048200000000,
    -2160000000000], [2381400000000, 4320000000000]) (some (0, 10, 10)) (some (0, 10, 10)) (.next
    ([-210000000000], [465000000000]) (some (0, 10, 10)) (some (0, 10, 10)) (.next ([-405000000000],
    [840000000000]) (some (0, 10, 10)) (some (1, 10, 10)) (.next ([-465000000000], [930000000000])
    (some (1, 10, 10)) (some (1, 10, 10)) (.next ([-195000000000], [375000000000]) (some (1, 10,
    10)) (some (1, 10, 10)) (.next ([-255000000000], [465000000000]) (some (1, 10, 10)) (some (1,
    10, 10)) (.next ([-1333200000000, -2160000000000], [2381400000000, 4320000000000]) (some (1, 10,
    10)) (some (2, 10, 10)) (.next ([-631800000000, 2160000000000], [1048200000000, 2160000000000])
    (some (2, 10, 10)) (some (2, 10, 10)) (.next ([-750000000000], [1215000000000]) (some (2, 10,
    10)) (some (2, 10, 10)) (.next ([-3750000000000], [5946000000000]) (some (2, 10, 10)) (some (2,
    10, 10)) (.next ([-421800000000, 2160000000000], [583200000000, 2160000000000]) (some (2, 10,
    8)) (some (2, 10, 8)) (.next ([-3876000000000], [5340000000000]) (some (2, 10, 8)) (some (2, 10,
    8)) (.next ([-1588200000000, -2160000000000], [2171400000000, 4320000000000]) (some (2, 10, 8))
    (some (2, 10, 8)) (.next ([-4161000000000], [5625000000000]) (some (2, 10, 8)) (some (2, 10, 8))
    (.next ([-4626000000000], [5880000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next
    ([-1590000000000], [1935000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next
    ([-1215000000000], [1470000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next
    ([-5091000000000], [6090000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next
    ([-5376000000000], [6090000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next ([-1798200000000,
    -2160000000000], [1916400000000, 4320000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next
    ([-5631000000000], [5880000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next
    ([-1590000000000], [1650000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.terminal (some (2, 10,
    8)) (some (2, 10, 8)) (some (2, 10, 8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan16Owner0Part1 : FanWitness := (.next ([345000000000], [1590000000000]) (some (9, 5, 10))
    (some (9, 5, 10)) (.next ([255000000000], [1215000000000]) (some (9, 5, 10)) (some (9, 5, 10))
    (.next ([999000000000], [5091000000000]) (some (9, 5, 10)) (some (9, 5, 10)) (.next
    ([714000000000], [5376000000000]) (some (9, 5, 10)) (some (9, 5, 10)) (.next ([118200000000,
    2160000000000], [1798200000000, 2160000000000]) (some (9, 5, 10)) (some (9, 5, 10)) (.next
    ([249000000000], [5631000000000]) (some (9, 5, 10)) (some (9, 5, 10)) (.next ([60000000000],
    [1590000000000]) (some (9, 5, 10)) (some (9, 5, 10)) (.next ([0], [285000000000]) (some (9, 5,
    10)) (some (9, 5, 10)) (.next ([-126000000000], [5811000000000]) (some (0, 6, 10)) (some (0, 6,
    10)) (.next ([-334200000000, -2160000000000], [5792400000000, 4320000000000]) (some (0, 6, 10))
    (some (0, 6, 10)) (.next ([-166800000000, 2160000000000], [1798200000000, 2160000000000]) (some
    (0, 6, 10)) (some (0, 6, 10)) (.next ([-195000000000], [1380000000000]) (some (0, 6, 10)) (some
    (0, 6, 10)) (.next ([-917400000000, -4320000000000], [5209200000000, 2160000000000]) (some (0,
    6, 10)) (some (0, 6, 10)) (.next ([-1680000000000], [9090000000000]) (some (0, 6, 10)) (some (0,
    6, 10)) (.next ([-1965000000000], [9375000000000]) (some (0, 6, 10)) (some (0, 6, 10)) (.next
    ([-2430000000000], [9630000000000]) (some (0, 6, 10)) (some (0, 6, 10)) (.next ([-210000000000],
    [750000000000]) (some (0, 6, 10)) (some (0, 6, 10)) (.next ([-2895000000000], [9840000000000])
    (some (0, 6, 10)) (some (0, 6, 10)) (.next ([-3180000000000], [9840000000000]) (some (0, 6, 10))
    (some (0, 6, 10)) (.next ([-3435000000000], [9630000000000]) (some (0, 6, 10)) (some (0, 6, 10))
    (.next ([-405000000000], [1125000000000]) (some (0, 6, 10)) (some (0, 6, 10)) (.next
    ([-3013200000000, -2160000000000], [8041800000000, -2160000000000]) (some (0, 6, 10)) (some (0,
    6, 10)) (.next ([-465000000000], [1215000000000]) (some (0, 6, 10)) (some (0, 6, 10)) (.next
    ([-3615000000000], [9435000000000]) (some (0, 6, 10)) (some (0, 6, 10))
    fan16Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan16Owner0Part2 : FanWitness := (.next ([6945000000000], [2895000000000]) (some (8, 3, 10))
    (some (8, 3, 10)) (.next ([6660000000000], [3180000000000]) (some (8, 3, 10)) (some (8, 3, 10))
    (.next ([6195000000000], [3435000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next
    ([720000000000], [405000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next ([5028600000000,
    -4320000000000], [3013200000000, 2160000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next
    ([750000000000], [465000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next ([5820000000000],
    [3615000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next ([5611800000000, -2160000000000],
    [3596400000000, 4320000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next ([791400000000,
    4320000000000], [601800000000, -2160000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next
    ([1333200000000, 2160000000000], [1048200000000, 2160000000000]) (some (8, 3, 10)) (some (8, 3,
    10)) (.next ([255000000000], [210000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next
    ([435000000000], [405000000000]) (some (8, 3, 10)) (some (8, 4, 10)) (.next ([465000000000],
    [465000000000]) (some (8, 4, 10)) (some (8, 4, 10)) (.next ([180000000000], [195000000000])
    (some (8, 4, 10)) (some (8, 4, 10)) (.next ([210000000000], [255000000000]) (some (8, 4, 10))
    (some (8, 5, 10)) (.next ([1048200000000, 2160000000000], [1333200000000, 2160000000000]) (some
    (8, 5, 10)) (some (8, 5, 10)) (.next ([416400000000, 4320000000000], [631800000000,
    -2160000000000]) (some (8, 5, 10)) (some (8, 5, 10)) (.next ([465000000000], [750000000000])
    (some (8, 5, 10)) (some (8, 5, 10)) (.next ([2196000000000], [3750000000000]) (some (8, 5, 10))
    (some (8, 5, 10)) (.next ([161400000000, 4320000000000], [421800000000, -2160000000000]) (some
    (8, 5, 10)) (some (8, 5, 10)) (.next ([1464000000000], [3876000000000]) (some (8, 5, 10)) (some
    (8, 5, 10)) (.next ([583200000000, 2160000000000], [1588200000000, 2160000000000]) (some (8, 5,
    10)) (some (9, 5, 10)) (.next ([1464000000000], [4161000000000]) (some (9, 5, 10)) (some (9, 5,
    10)) (.next ([1254000000000], [4626000000000]) (some (9, 5, 10)) (some (9, 5, 10))
    fan16Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan17Owner0Part0 : FanWitness := (.next ([-1333200000000, -2160000000000], [2381400000000,
    4320000000000]) (some (1, 10, 8)) (some (2, 10, 8)) (.next ([-631800000000, 2160000000000],
    [1048200000000, 2160000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next ([-5820000000000],
    [9465000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next ([-750000000000], [1215000000000])
    (some (2, 10, 8)) (some (2, 10, 8)) (.next ([-6105000000000], [9465000000000]) (some (2, 10, 8))
    (some (2, 10, 8)) (.next ([-4771800000000, 2160000000000], [7083600000000, -4320000000000])
    (some (2, 10, 8)) (some (2, 10, 8)) (.next ([-6360000000000], [9255000000000]) (some (2, 10, 8))
    (some (2, 10, 8)) (.next ([-1215000000000], [1755000000000]) (some (2, 10, 8)) (some (2, 10, 8))
    (.next ([-540000000000], [750000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next
    ([-3876000000000], [5340000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next ([-1588200000000,
    -2160000000000], [2171400000000, 4320000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next
    ([-4161000000000], [5625000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next
    ([-6570000000000], [8715000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next
    ([-6360000000000], [8250000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next ([-5938200000000,
    -2160000000000], [7666800000000, -2160000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next
    ([-6165000000000], [7875000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next
    ([-4626000000000], [5880000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next
    ([-1590000000000], [1935000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next
    ([-1215000000000], [1470000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next
    ([-5091000000000], [6090000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next
    ([-5376000000000], [6090000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next ([-1798200000000,
    -2160000000000], [1916400000000, 4320000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next
    ([-5631000000000], [5880000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.next
    ([-1590000000000], [1650000000000]) (some (2, 10, 8)) (some (2, 10, 8)) (.terminal (some (2, 10,
    8)) (some (2, 10, 8)) (some (2, 10, 8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan17Owner0Part1 : FanWitness := (.next ([345000000000], [1590000000000]) (some (9, 10, 10))
    (some (9, 10, 10)) (.next ([255000000000], [1215000000000]) (some (9, 10, 10)) (some (9, 10,
    10)) (.next ([999000000000], [5091000000000]) (some (9, 10, 10)) (some (9, 10, 10)) (.next
    ([714000000000], [5376000000000]) (some (9, 10, 10)) (some (9, 10, 10)) (.next ([118200000000,
    2160000000000], [1798200000000, 2160000000000]) (some (9, 10, 10)) (some (9, 10, 10)) (.next
    ([249000000000], [5631000000000]) (some (9, 10, 10)) (some (9, 10, 10)) (.next ([60000000000],
    [1590000000000]) (some (9, 10, 10)) (some (9, 10, 10)) (.next ([0], [285000000000]) (some (9,
    10, 10)) (some (9, 10, 10)) (.next ([-126000000000], [5811000000000]) (some (0, 10, 10)) (some
    (0, 10, 10)) (.next ([-334200000000, -2160000000000], [5792400000000, 4320000000000]) (some (0,
    10, 10)) (some (0, 10, 10)) (.next ([-166800000000, 2160000000000], [1798200000000,
    2160000000000]) (some (0, 10, 10)) (some (0, 10, 8)) (.next ([-195000000000], [1380000000000])
    (some (0, 10, 8)) (some (0, 10, 8)) (.next ([-917400000000, -4320000000000], [5209200000000,
    2160000000000]) (some (0, 10, 8)) (some (0, 10, 8)) (.next ([-421800000000, 2160000000000],
    [1588200000000, 2160000000000]) (some (0, 10, 8)) (some (0, 10, 8)) (.next ([-210000000000],
    [750000000000]) (some (0, 10, 8)) (some (0, 10, 8)) (.next ([-405000000000], [1125000000000])
    (some (0, 10, 8)) (some (0, 10, 8)) (.next ([-465000000000], [1215000000000]) (some (0, 10, 8))
    (some (0, 10, 8)) (.next ([-601800000000, 2160000000000], [1393200000000, 2160000000000]) (some
    (0, 10, 8)) (some (0, 10, 8)) (.next ([-1048200000000, -2160000000000], [2381400000000,
    4320000000000]) (some (0, 10, 8)) (some (0, 10, 8)) (.next ([-210000000000], [465000000000])
    (some (0, 10, 8)) (some (0, 10, 8)) (.next ([-405000000000], [840000000000]) (some (0, 10, 8))
    (some (1, 10, 8)) (.next ([-465000000000], [930000000000]) (some (1, 10, 8)) (some (1, 10, 8))
    (.next ([-195000000000], [375000000000]) (some (1, 10, 8)) (some (1, 10, 8)) (.next
    ([-255000000000], [465000000000]) (some (1, 10, 8)) (some (1, 10, 8))
    fan17Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan17Owner0Part2 : FanWitness := (.next ([791400000000, 4320000000000], [601800000000,
    -2160000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next ([1333200000000, 2160000000000],
    [1048200000000, 2160000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next ([255000000000],
    [210000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next ([435000000000], [405000000000])
    (some (8, 3, 10)) (some (8, 4, 10)) (.next ([465000000000], [465000000000]) (some (8, 4, 10))
    (some (8, 4, 10)) (.next ([180000000000], [195000000000]) (some (8, 4, 10)) (some (8, 4, 10))
    (.next ([210000000000], [255000000000]) (some (8, 4, 10)) (some (8, 5, 10)) (.next
    ([1048200000000, 2160000000000], [1333200000000, 2160000000000]) (some (8, 5, 10)) (some (8, 5,
    10)) (.next ([416400000000, 4320000000000], [631800000000, -2160000000000]) (some (8, 5, 10))
    (some (8, 5, 10)) (.next ([3645000000000], [5820000000000]) (some (8, 5, 10)) (some (8, 5, 10))
    (.next ([465000000000], [750000000000]) (some (8, 5, 10)) (some (8, 5, 10)) (.next
    ([3360000000000], [6105000000000]) (some (8, 5, 10)) (some (8, 5, 10)) (.next ([2311800000000,
    -2160000000000], [4771800000000, -2160000000000]) (some (8, 5, 10)) (some (8, 5, 10)) (.next
    ([2895000000000], [6360000000000]) (some (8, 5, 10)) (some (8, 5, 10)) (.next ([540000000000],
    [1215000000000]) (some (8, 5, 10)) (some (8, 5, 10)) (.next ([210000000000], [540000000000])
    (some (8, 5, 10)) (some (8, 5, 10)) (.next ([1464000000000], [3876000000000]) (some (8, 5, 10))
    (some (8, 5, 10)) (.next ([583200000000, 2160000000000], [1588200000000, 2160000000000]) (some
    (8, 5, 10)) (some (9, 5, 10)) (.next ([1464000000000], [4161000000000]) (some (9, 5, 10)) (some
    (9, 5, 10)) (.next ([2145000000000], [6570000000000]) (some (9, 5, 10)) (some (9, 5, 10)) (.next
    ([1890000000000], [6360000000000]) (some (9, 5, 10)) (some (9, 5, 10)) (.next ([1728600000000,
    -4320000000000], [5938200000000, 2160000000000]) (some (9, 5, 10)) (some (9, 5, 10)) (.next
    ([1710000000000], [6165000000000]) (some (9, 5, 10)) (some (9, 5, 10)) (.next ([1254000000000],
    [4626000000000]) (some (9, 5, 10)) (some (9, 10, 10)) fan17Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner2Part0 : FanWitness := (.next ([2925000000000], [3000000000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([2925000000000, -9000000000000], [3375000000000, 0]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([2805000000000], [3765000000000]) (some (0, 1, 3)) (some (0, 1, 3))
    (.next ([2355000000000], [3450000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([120000000000], [180000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2355000000000],
    [3645000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2430000000000, 0], [4140000000000,
    -9000000000000]) (some (0, 1, 3)) (some (0, 1, 4)) (.next ([945000000000, -9000000000000],
    [2700000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([75000000000, 0],
    [495000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0, 0],
    [4860000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0, -9000000000000],
    [375000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2055000000000, -9000000000000],
    [8625000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2430000000000,
    -9000000000000], [9000000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2505000000000,
    -9000000000000], [8505000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
    ([-2700000000000], [5805000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-3000000000000],
    [5925000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-3375000000000, 0], [6300000000000,
    -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-3765000000000], [6570000000000])
    (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-3450000000000], [5805000000000]) (some (0, 1, 4))
    (some (0, 1, 4)) (.next ([-180000000000], [300000000000]) (some (0, 1, 4)) (some (0, 1, 4))
    (.next ([-3645000000000], [6000000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next
    ([-4140000000000, 9000000000000], [6570000000000, -9000000000000]) (some (0, 2, 4)) (some (0, 2,
    4)) (.next ([-2700000000000, -9000000000000], [3645000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([-495000000000, 9000000000000], [570000000000, -9000000000000]) (some (0, 2, 4)) (some
    (5, 2, 4)) (.terminal (some (5, 2, 4)) (some (5, 2, 0)) (some (5, 2,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner2Part0 : FanWitness := (.next ([6570000000000, -9000000000000], [2430000000000,
    9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([6000000000000, 0], [2505000000000,
    9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([3105000000000], [3645000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2805000000000], [3765000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([120000000000], [180000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([2355000000000], [3645000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([2430000000000, 0], [4140000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next
    ([75000000000, 0], [495000000000, -9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([180000000000], [2145000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([390000000000,
    -9000000000000], [6180000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0,
    0], [4860000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0,
    -9000000000000], [2820000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0,
    -9000000000000], [375000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2055000000000,
    -9000000000000], [8625000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
    ([-2430000000000, -9000000000000], [9000000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
    ([-2505000000000, -9000000000000], [8505000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1,
    4)) (.next ([-3645000000000], [6750000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
    ([-3765000000000], [6570000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-180000000000],
    [300000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-3645000000000], [6000000000000])
    (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-4140000000000, 9000000000000], [6570000000000,
    -9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-495000000000, 9000000000000],
    [570000000000, -9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2145000000000],
    [2325000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-6180000000000, -9000000000000],
    [6570000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2, 4)) (some (5, 2, 0))
    (some (5, 2, 4)))))))))))))))))))))))))))

theorem excluded16_0 : ExcludedOn (model16.B 0 ++ [step16.q]) 9000000000000 (model16.caps 0)
    (model16.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5685000000000], [126000000000]) (some (8, 2,
      10)) (some (8, 3, 10)) (.next ([5458200000000, 2160000000000], [334200000000, 2160000000000])
      (some (8, 3, 10)) (some (8, 3, 10)) (.next ([1631400000000, 4320000000000], [166800000000,
      -2160000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next ([1185000000000], [195000000000])
      (some (8, 3, 10)) (some (8, 3, 10)) (.next ([4291800000000, -2160000000000], [917400000000,
      4320000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next ([7410000000000], [1680000000000])
      (some (8, 3, 10)) (some (8, 3, 10)) (.next ([7410000000000], [1965000000000]) (some (8, 3,
      10)) (some (8, 3, 10)) (.next ([7200000000000], [2430000000000]) (some (8, 3, 10)) (some (8,
      3, 10)) (.next ([540000000000], [210000000000]) (some (8, 3, 10)) (some (8, 3, 10))
      fan16Owner0Part2)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_1 : ExcludedOn (model16.B 1 ++ [step16.q]) 9000000000000 (model16.caps 1)
    (model16.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([375000000000, -9000000000000], [0,
      9000000000000]) none none (.next ([2805000000000], [2235000000000]) none none (.next
      ([2430000000000, 9000000000000], [2235000000000, -9000000000000]) none none (.next
      ([2430000000000, 9000000000000], [2430000000000, 9000000000000]) none none (.next
      ([2055000000000, 9000000000000], [2805000000000]) none none (.next ([0], [7095000000000,
      9000000000000]) none none (.next ([0, -9000000000000], [375000000000, 0]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-2235000000000], [5040000000000]) (some (3, 1, 2)) none (.next
      ([-2235000000000, 9000000000000], [4665000000000, 0]) none none (.next ([-2430000000000,
      -9000000000000], [4860000000000, 18000000000000]) none none (.next ([-2805000000000],
      [4860000000000, 9000000000000]) none none (.terminal none none none))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_3 : ExcludedOn (model16.B 3 ++ [step16.q]) 9000000000000 (model16.caps 3)
    (model16.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_4 : ExcludedOn (model16.B 4 ++ [step16.q]) 9000000000000 (model16.caps 4)
    (model16.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_5 : ExcludedOn (model16.B 5 ++ [step16.q]) 9000000000000 (model16.caps 5)
    (model16.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_6 : ExcludedOn (model16.B 6 ++ [step16.q]) 9000000000000 (model16.caps 6)
    (model16.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_7 : ExcludedOn (model16.B 7 ++ [step16.q]) 9000000000000 (model16.caps 7)
    (model16.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([375000000000, -9000000000000], [0,
      9000000000000]) (some (2, 4, 1)) (some (3, 4, 2)) (.next ([2805000000000], [2985000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([2430000000000, 9000000000000], [2985000000000,
      -9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1155000000000, -9000000000000],
      [2430000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([2430000000000,
      9000000000000], [6570000000000, -9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([375000000000, -9000000000000], [6570000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([0, 0], [6570000000000, -9000000000000]) (some (3, 4, 2)) (some (4, 4, 2)) (.next ([0,
      -9000000000000], [375000000000, 0]) (some (4, 4, 2)) (some (4, 4, 2)) (.next
      ([-2985000000000], [5790000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-2985000000000,
      9000000000000], [5415000000000, 0]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-2430000000000,
      -9000000000000], [3585000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([-6570000000000,
      9000000000000], [9000000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-6570000000000,
      0], [6945000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.terminal (some (4, 1,
      2)) (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_8 : ExcludedOn (model16.B 8 ++ [step16.q]) 9000000000000 (model16.caps 8)
    (model16.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_9 : ExcludedOn (model16.B 9 ++ [step16.q]) 9000000000000 (model16.caps 9)
    (model16.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded16_3
    · exact excluded16_4
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5685000000000], [126000000000]) (some (8, 2,
      10)) (some (8, 3, 10)) (.next ([5458200000000, 2160000000000], [334200000000, 2160000000000])
      (some (8, 3, 10)) (some (8, 3, 10)) (.next ([1631400000000, 4320000000000], [166800000000,
      -2160000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next ([1185000000000], [195000000000])
      (some (8, 3, 10)) (some (8, 3, 10)) (.next ([4291800000000, -2160000000000], [917400000000,
      4320000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next ([1166400000000, 4320000000000],
      [421800000000, -2160000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next ([540000000000],
      [210000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next ([720000000000], [405000000000])
      (some (8, 3, 10)) (some (8, 3, 10)) (.next ([750000000000], [465000000000]) (some (8, 3, 10))
      (some (8, 3, 10)) fan17Owner0Part2)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded17_1 : ExcludedOn (model17.B 1 ++ [step17.q]) 9000000000000 (model17.caps 1)
    (model17.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3645000000000, 0], [1680000000000,
      9000000000000]) none none (.next ([750000000000], [465000000000, -9000000000000]) (some (2, 3,
      2)) (some (2, 3, 2)) (.next ([2430000000000, 9000000000000], [2235000000000, -9000000000000])
      (some (2, 3, 2)) (some (2, 3, 2)) (.next ([2430000000000, 9000000000000], [2430000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([750000000000], [7560000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0], [7095000000000, 9000000000000]) (some (0, 3,
      2)) (some (0, 3, 2)) (.next ([-1680000000000, -9000000000000], [5325000000000, 9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-465000000000, 9000000000000], [1215000000000,
      -9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-2235000000000, 9000000000000],
      [4665000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2430000000000,
      -9000000000000], [4860000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-7560000000000], [8310000000000]) (some (3, 1, 2)) none (.terminal none none
      none))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded17_2 : ExcludedOn (model17.B 2 ++ [step17.q]) 9000000000000 (model17.caps 2)
    (model17.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_3 : ExcludedOn (model17.B 3 ++ [step17.q]) 9000000000000 (model17.caps 3)
    (model17.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_4 : ExcludedOn (model17.B 4 ++ [step17.q]) 9000000000000 (model17.caps 4)
    (model17.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_5 : ExcludedOn (model17.B 5 ++ [step17.q]) 9000000000000 (model17.caps 5)
    (model17.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_7 : ExcludedOn (model17.B 7 ++ [step17.q]) 9000000000000 (model17.caps 7)
    (model17.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_8 : ExcludedOn (model17.B 8 ++ [step17.q]) 9000000000000 (model17.caps 8)
    (model17.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_9 : ExcludedOn (model17.B 9 ++ [step17.q]) 9000000000000 (model17.caps 9)
    (model17.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded17_4
    · exact excluded17_5
    · exact (hj rfl).elim
    · exact excluded17_7
    · exact excluded17_8
    · exact excluded17_9
theorem next17 : model17.insert step17 = model18 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded18_1 : ExcludedOn (model18.B 1 ++ [step18.q]) 9000000000000 (model18.caps 1)
    (model18.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7785000000000, 9000000000000], [945000000000,
      -9000000000000]) none none (.next ([2430000000000, 9000000000000], [2235000000000,
      -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2430000000000, 9000000000000],
      [2430000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2925000000000,
      -9000000000000], [3375000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([690000000000],
      [8040000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0], [7095000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-945000000000, 9000000000000],
      [8730000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2235000000000, 9000000000000],
      [4665000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2430000000000,
      -9000000000000], [4860000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-3375000000000, 0], [6300000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-8040000000000], [8730000000000]) (some (3, 1, 2)) none (.terminal none none
      none))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded18_2 : ExcludedOn (model18.B 2 ++ [step18.q]) 9000000000000 (model18.caps 2)
    (model18.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([375000000000, -9000000000000], [0,
      9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([6570000000000, 0], [2055000000000,
      9000000000000]) (some (0, 5, 2)) (some (0, 5, 3)) (.next ([6570000000000, -9000000000000],
      [2430000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([6000000000000, 0],
      [2505000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([3105000000000],
      [2700000000000]) (some (0, 5, 3)) (some (0, 5, 3)) fan18Owner2Part0)))))) (den :=
      9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_3 : ExcludedOn (model18.B 3 ++ [step18.q]) 9000000000000 (model18.caps 3)
    (model18.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3645000000000, 0], [3195000000000,
      -9000000000000]) (some (1, 0, 3)) (some (2, 0, 3)) (.next ([2430000000000, 9000000000000],
      [2430000000000, 9000000000000]) (some (2, 0, 3)) (some (2, 0, 3)) (.next ([3645000000000],
      [5625000000000]) (some (2, 0, 3)) (some (2, 0, 3)) (.next ([1215000000000, -9000000000000],
      [8055000000000, 9000000000000]) (some (2, 0, 3)) (some (2, 0, 3)) (.next ([0], [2430000000000,
      9000000000000]) (some (2, 0, 3)) (some (2, 3, 3)) (.next ([-3195000000000, 9000000000000],
      [6840000000000, -9000000000000]) (some (0, 3, 3)) (some (0, 3, 3)) (.next ([-2430000000000,
      -9000000000000], [4860000000000, 18000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([-5625000000000], [9270000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-8055000000000,
      -9000000000000], [9270000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.terminal (some (0, 3,
      1)) (some (0, 3, 1)) (some (0, 3, 1))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_4 : ExcludedOn (model18.B 4 ++ [step18.q]) 9000000000000 (model18.caps 4)
    (model18.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_5 : ExcludedOn (model18.B 5 ++ [step18.q]) 9000000000000 (model18.caps 5)
    (model18.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_6 : ExcludedOn (model18.B 6 ++ [step18.q]) 9000000000000 (model18.caps 6)
    (model18.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_7 : ExcludedOn (model18.B 7 ++ [step18.q]) 9000000000000 (model18.caps 7)
    (model18.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_8 : ExcludedOn (model18.B 8 ++ [step18.q]) 9000000000000 (model18.caps 8)
    (model18.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_9 : ExcludedOn (model18.B 9 ++ [step18.q]) 9000000000000 (model18.caps 9)
    (model18.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked18 : StepValid model18 9000000000000 step18 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded18_1
    · exact excluded18_2
    · exact excluded18_3
    · exact excluded18_4
    · exact excluded18_5
    · exact excluded18_6
    · exact excluded18_7
    · exact excluded18_8
    · exact excluded18_9
theorem next18 : model18.insert step18 = model19 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded19_1 : ExcludedOn (model19.B 1 ++ [step19.q]) 9000000000000 (model19.caps 1)
    (model19.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_2 : ExcludedOn (model19.B 2 ++ [step19.q]) 9000000000000 (model19.caps 2)
    (model19.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_3 : ExcludedOn (model19.B 3 ++ [step19.q]) 9000000000000 (model19.caps 3)
    (model19.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_4 : ExcludedOn (model19.B 4 ++ [step19.q]) 9000000000000 (model19.caps 4)
    (model19.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_5 : ExcludedOn (model19.B 5 ++ [step19.q]) 9000000000000 (model19.caps 5)
    (model19.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6315000000000, -9000000000000], [810000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([2430000000000, 9000000000000],
      [2430000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([4050000000000,
      9000000000000], [4695000000000, -9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next
      ([1620000000000], [7125000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0],
      [2430000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-810000000000,
      -9000000000000], [7125000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-2430000000000,
      -9000000000000], [4860000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-4695000000000, 9000000000000], [8745000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-7125000000000], [8745000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_6 : ExcludedOn (model19.B 6 ++ [step19.q]) 9000000000000 (model19.caps 6)
    (model19.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7125000000000], [255000000000]) (some (4, 0, 1))
      (some (4, 0, 2)) (.next ([5355000000000], [750000000000]) (some (4, 0, 2)) (some (4, 0, 2))
      (.next ([2925000000000, -9000000000000], [750000000000]) (some (4, 0, 2)) (some (4, 0, 2))
      (.next ([4695000000000, -9000000000000], [2685000000000, 9000000000000]) (some (4, 0, 2))
      (some (4, 0, 3)) (.next ([2430000000000, 9000000000000], [2430000000000, 9000000000000]) (some
      (4, 0, 3)) (some (4, 0, 3)) (.next ([2175000000000, 9000000000000], [4950000000000,
      -9000000000000]) (some (4, 0, 3)) (some (4, 0, 3)) (.next ([1680000000000, 9000000000000],
      [6105000000000]) (some (4, 0, 3)) (some (4, 0, 3)) (.next ([1020000000000], [5610000000000])
      (some (4, 0, 3)) (some (4, 0, 3)) (.next ([0, 0], [2430000000000, 9000000000000]) (some (4, 0,
      3)) (some (4, 0, 3)) (.next ([-255000000000], [7380000000000]) (some (4, 0, 3)) (some (4, 1,
      3)) (.next ([-750000000000], [6105000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-750000000000], [3675000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-2685000000000, -9000000000000], [7380000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-2430000000000, -9000000000000], [4860000000000, 18000000000000]) (some (4, 1, 3)) (some (4,
      1, 3)) (.next ([-4950000000000, 9000000000000], [7125000000000]) (some (4, 1, 3)) (some (4, 1,
      3)) (.next ([-6105000000000, 0], [7785000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([-5610000000000], [6630000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal
      (some (0, 1, 3)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_7 : ExcludedOn (model19.B 7 ++ [step19.q]) 9000000000000 (model19.caps 7)
    (model19.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_8 : ExcludedOn (model19.B 8 ++ [step19.q]) 9000000000000 (model19.caps 8)
    (model19.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_9 : ExcludedOn (model19.B 9 ++ [step19.q]) 9000000000000 (model19.caps 9)
    (model19.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked19 : StepValid model19 9000000000000 step19 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded19_1
    · exact excluded19_2
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

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2820000000000, -9000000000000], [0,
      9000000000000]) none none (.next ([4860000000000, 9000000000000], [390000000000,
      -9000000000000]) none none (.next ([5250000000000], [2235000000000]) none none (.next
      ([2430000000000, 9000000000000], [2235000000000, -9000000000000]) none none (.next
      ([2430000000000, 9000000000000], [2430000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([0], [7095000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0,
      -9000000000000], [2820000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-390000000000,
      9000000000000], [5250000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2235000000000],
      [7485000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2235000000000, 9000000000000],
      [4665000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2430000000000,
      -9000000000000], [4860000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal
      (some (3, 1, 2)) none none))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_2 : ExcludedOn (model20.B 2 ++ [step20.q]) 9000000000000 (model20.caps 2)
    (model20.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2820000000000, -9000000000000], [0,
      9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([375000000000, -9000000000000], [0,
      9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([6570000000000, 0], [2055000000000,
      9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) fan20Owner2Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_3 : ExcludedOn (model20.B 3 ++ [step20.q]) 9000000000000 (model20.caps 3)
    (model20.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_4 : ExcludedOn (model20.B 4 ++ [step20.q]) 9000000000000 (model20.caps 4)
    (model20.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_5 : ExcludedOn (model20.B 5 ++ [step20.q]) 9000000000000 (model20.caps 5)
    (model20.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_6 : ExcludedOn (model20.B 6 ++ [step20.q]) 9000000000000 (model20.caps 6)
    (model20.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_7 : ExcludedOn (model20.B 7 ++ [step20.q]) 9000000000000 (model20.caps 7)
    (model20.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_8 : ExcludedOn (model20.B 8 ++ [step20.q]) 9000000000000 (model20.caps 8)
    (model20.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_9 : ExcludedOn (model20.B 9 ++ [step20.q]) 9000000000000 (model20.caps 9)
    (model20.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked20 : StepValid model20 9000000000000 step20 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded20_1
    · exact excluded20_2
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

end Aown270000280000
end ConwaySoifer.Simplified.Certificates
