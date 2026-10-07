/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext110000120000
import Mathlib.Tactic.FinCases

/-!
# Sext 110000 120000 6

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
namespace Sext110000120000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner3Part0 : FanWitness := (.next ([615000000000], [2640000000000]) (some (5, 6, 3)) (some
    (5, 6, 3)) (.next ([990000000000, 9000000000000], [6000000000000]) (some (5, 6, 3)) (some (5, 6,
    3)) (.next ([495000000000], [4875000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([0,
    9000000000000], [3000000000000, -9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([0,
    9000000000000], [6000000000000]) (some (5, 6, 3)) (some (5, 6, 4)) (.next ([0], [990000000000])
    (some (5, 6, 4)) (some (5, 6, 4)) (.next ([-270000000000], [5010000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-630000000000], [5505000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-630000000000], [4515000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-990000000000], [6000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-990000000000],
    [3990000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-885000000000], [2370000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1260000000000], [3270000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-3270000000000, 9000000000000], [8010000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-3000000000000], [6990000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-3000000000000], [6000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-2250000000000], [4260000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-4260000000000],
    [8010000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3885000000000, 9000000000000],
    [5370000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2640000000000], [3255000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-6000000000000, 0], [6990000000000, 9000000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4875000000000], [5370000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([-3000000000000, 9000000000000], [3000000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([-6000000000000, 0], [6000000000000, 9000000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan49Owner3Part0 : FanWitness := (.next ([495000000000], [1515000000000]) (some (5, 0, 6)) (some
    (5, 0, 6)) (.next ([990000000000, 9000000000000], [6000000000000]) (some (5, 0, 6)) (some (5, 0,
    6)) (.next ([495000000000], [4875000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([0,
    9000000000000], [3000000000000, -9000000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([0,
    9000000000000], [6000000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([0], [990000000000])
    (some (5, 0, 6)) (some (5, 0, 6)) (.next ([-390000000000], [3885000000000]) (some (0, 0, 6))
    (some (0, 1, 6)) (.next ([-630000000000], [5505000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-630000000000], [4515000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-990000000000], [6000000000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-990000000000],
    [3990000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-885000000000], [2370000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-3000000000000], [6990000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-3000000000000], [6000000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-4515000000000], [9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-4515000000000], [8010000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-2010000000000,
    9000000000000], [3495000000000, -9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-3000000000000], [4485000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-3885000000000,
    9000000000000], [5370000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1515000000000],
    [2010000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-6000000000000, 0], [6990000000000,
    9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4875000000000], [5370000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-3000000000000, 9000000000000], [3000000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-6000000000000, 0], [6000000000000, 9000000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan50Owner2Part0 : FanWitness := (.next ([1890000000000, 9000000000000], [3150000000000,
    -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([3360000000000], [5640000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([990000000000], [4260000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([900000000000], [4140000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([990000000000, 9000000000000], [6000000000000, 0]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([0], [1485000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-495000000000,
    9000000000000], [6000000000000, 0]) (some (0, 6, 4)) (some (0, 6, 5)) (.next ([-750000000000],
    [5010000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-960000000000], [5100000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-750000000000], [3525000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-1485000000000], [6000000000000]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-960000000000], [3615000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-1155000000000], [4155000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-1380000000000],
    [3750000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-1500000000000], [3960000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2640000000000], [5640000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-4650000000000, 9000000000000], [9000000000000, 0]) (some (0, 2, 5))
    (some (6, 2, 5)) (.next ([-120000000000], [210000000000]) (some (6, 2, 5)) (some (6, 2, 5))
    (.next ([-3270000000000, 9000000000000], [5250000000000, 0]) (some (6, 2, 5)) (some (6, 3, 5))
    (.next ([-3150000000000, 9000000000000], [5040000000000, 0]) (some (6, 3, 5)) (some (6, 3, 5))
    (.next ([-5640000000000], [9000000000000]) (some (6, 3, 5)) (some (6, 4, 5)) (.next
    ([-4260000000000], [5250000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-4140000000000],
    [5040000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-6000000000000, 0], [6990000000000,
    9000000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.terminal (some (6, 4, 5)) (some (6, 4, 0))
    (some (6, 4, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan51Owner3Part0 : FanWitness := (.next ([1500000000000], [2430000000000]) (some (5, 0, 6))
    (some (5, 0, 6)) (.next ([990000000000], [1650000000000]) (some (5, 0, 6)) (some (5, 0, 6))
    (.next ([990000000000, 9000000000000], [4650000000000, -9000000000000]) (some (5, 0, 6)) (some
    (5, 0, 6)) (.next ([990000000000, 9000000000000], [6000000000000]) (some (5, 0, 6)) (some (5, 0,
    6)) (.next ([0, 9000000000000], [3000000000000, -9000000000000]) (some (5, 0, 6)) (some (5, 0,
    6)) (.next ([0, 9000000000000], [6000000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([0],
    [990000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([-360000000000], [6000000000000])
    (some (0, 0, 6)) (some (0, 1, 6)) (.next ([-360000000000], [5010000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-1500000000000], [9420000000000]) (some (0, 1, 6)) (some (0, 2, 6))
    (.next ([-990000000000], [6000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-1500000000000], [8430000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-990000000000],
    [3990000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1140000000000], [3420000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-2430000000000, 9000000000000], [6930000000000,
    -9000000000000]) (some (0, 2, 6)) (some (0, 6, 6)) (.next ([-3000000000000], [6990000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3420000000000], [7920000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-3000000000000], [6000000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-2430000000000], [3930000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-1650000000000], [2640000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-4650000000000,
    9000000000000], [5640000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-6000000000000, 0],
    [6990000000000, 9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3000000000000,
    9000000000000], [3000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-6000000000000, 0],
    [6000000000000, 9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.terminal (some (0, 6, 4))
    (some (0, 6, 4)) (some (0, 6, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan52Owner3Part0 : FanWitness := (.next ([1800000000000, 9000000000000], [7200000000000,
    -9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([990000000000, 9000000000000],
    [4650000000000, -9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([990000000000,
    9000000000000], [6000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([810000000000],
    [8190000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([0, 9000000000000], [3000000000000,
    -9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([0, 9000000000000], [6000000000000])
    (some (5, 6, 3)) (some (5, 6, 4)) (.next ([0], [990000000000]) (some (5, 6, 4)) (some (5, 6, 4))
    (.next ([-360000000000], [6000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-360000000000], [5010000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-990000000000],
    [6000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-990000000000], [3990000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3000000000000], [6990000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-3000000000000], [6000000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-4200000000000], [7200000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-1650000000000], [2640000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-5190000000000],
    [8190000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-4200000000000], [6000000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2550000000000], [3360000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-7200000000000, 9000000000000], [9000000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-4650000000000, 9000000000000], [5640000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-6000000000000, 0], [6990000000000, 9000000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-8190000000000], [9000000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-3000000000000, 9000000000000], [3000000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-6000000000000, 0], [6000000000000, 9000000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.terminal (some (0, 6, 4)) (some (0, 6, 4)) (some (0, 6, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan52Owner4Part0 : FanWitness := (.next ([5625000000000], [870000000000]) (some (4, 1, 5)) (some
    (4, 1, 5)) (.next ([4260000000000], [990000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([5250000000000], [1740000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([495000000000],
    [375000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2190000000000], [6000000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([990000000000], [2940000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([495000000000], [2565000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([990000000000, 9000000000000], [6000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([990000000000, 9000000000000], [7200000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1,
    5)) (.next ([495000000000, 9000000000000], [4635000000000, -9000000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([0, 9000000000000], [4260000000000, -9000000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([0], [6000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([-495000000000], [5625000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-870000000000],
    [6495000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-990000000000], [5250000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1740000000000], [6990000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-375000000000], [870000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-6000000000000], [8190000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-2940000000000], [3930000000000]) (some (0, 1, 5)) (some (0, 5, 5)) (.next ([-2565000000000],
    [3060000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-6000000000000], [6990000000000,
    9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-7200000000000, 9000000000000],
    [8190000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4635000000000, 9000000000000],
    [5130000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4260000000000, 9000000000000],
    [4260000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3)) (some (0, 5, 4))
    (some (0, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan53Owner2Part0 : FanWitness := (.next ([4500000000000], [420000000000]) (some (0, 1, 5)) (some
    (0, 1, 5)) (.next ([3015000000000], [420000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([4515000000000], [1485000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([5040000000000],
    [3960000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([2040000000000, 0], [2010000000000,
    -9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([3555000000000], [3960000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([2040000000000], [3000000000000]) (some (0, 2, 3))
    (some (0, 2, 3)) (.next ([2070000000000, 9000000000000], [3510000000000, -9000000000000]) (some
    (0, 2, 3)) (some (0, 2, 3)) (.next ([1080000000000], [4500000000000]) (some (0, 2, 3)) (some (0,
    2, 3)) (.next ([990000000000, 9000000000000], [6000000000000, 0]) (some (0, 2, 3)) (some (0, 2,
    3)) (.next ([540000000000], [3540000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([0],
    [1485000000000]) (some (0, 2, 3)) (some (0, 5, 3)) (.next ([-495000000000, 9000000000000],
    [6000000000000, 0]) (some (0, 5, 3)) (some (0, 5, 4)) (.next ([-420000000000], [4920000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-420000000000], [3435000000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.next ([-1485000000000], [6000000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-3960000000000], [9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-2010000000000, 9000000000000], [4050000000000, -9000000000000]) (some (0, 5, 4)) (some (0, 5,
    4)) (.next ([-3960000000000], [7515000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-3000000000000], [5040000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3510000000000,
    9000000000000], [5580000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-4500000000000],
    [5580000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-6000000000000, 0], [6990000000000,
    9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3540000000000], [4080000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5, 4)) (some (0, 5, 0)) (some (0, 5,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan54Owner1Part0 : FanWitness := (.next ([3960000000000], [2040000000000]) (some (0, 5, 2))
    (some (0, 5, 2)) (.next ([2400000000000, -9000000000000], [1485000000000, 0]) (some (0, 5, 2))
    (some (0, 5, 2)) (.next ([5265000000000], [3555000000000]) (some (0, 5, 2)) (some (0, 5, 2))
    (.next ([2970000000000, -9000000000000], [2040000000000, 0]) (some (0, 5, 2)) (some (0, 5, 2))
    (.next ([570000000000], [555000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next
    ([4710000000000], [4680000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([990000000000,
    9000000000000], [990000000000, 9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next
    ([1320000000000], [4440000000000, -9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next
    ([1320000000000], [5430000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([330000000000,
    -9000000000000], [6420000000000, 9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([0],
    [990000000000, 9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([-495000000000,
    9000000000000], [4875000000000]) (some (0, 5, 2)) (some (0, 5, 3)) (.next ([-1050000000000,
    9000000000000], [6000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1485000000000],
    [4875000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2040000000000], [6000000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1485000000000, 0], [3885000000000, -9000000000000])
    (some (0, 5, 3)) none (.next ([-3555000000000], [8820000000000]) none none (.next
    ([-2040000000000, 0], [5010000000000, -9000000000000]) none none (.next ([-555000000000],
    [1125000000000]) none none (.next ([-4680000000000], [9390000000000]) none none (.next
    ([-990000000000, -9000000000000], [1980000000000, 18000000000000]) none none (.next
    ([-4440000000000, 9000000000000], [5760000000000, -9000000000000]) none none (.next
    ([-5430000000000], [6750000000000]) (some (5, 1, 0)) (some (5, 1, 0)) (.next ([-6420000000000,
    -9000000000000], [6750000000000, 0]) (some (5, 1, 0)) (some (5, 1, 0)) (.terminal (some (5, 1,
    0)) (some (5, 1, 0)) (some (5, 1, 0)))))))))))))))))))))))))))

theorem excluded48_0 : ExcludedOn (model48.B 0 ++ [step48.q]) 9000000000000 (model48.caps 0)
    (model48.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_1 : ExcludedOn (model48.B 1 ++ [step48.q]) 9000000000000 (model48.caps 1)
    (model48.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_2 : ExcludedOn (model48.B 2 ++ [step48.q]) 9000000000000 (model48.caps 2)
    (model48.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_3 : ExcludedOn (model48.B 3 ++ [step48.q]) 9000000000000 (model48.caps 3)
    (model48.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4740000000000], [270000000000]) (some (4, 0, 2))
      (some (5, 0, 2)) (.next ([4875000000000], [630000000000]) (some (5, 0, 2)) (some (5, 0, 2))
      (.next ([3885000000000], [630000000000]) (some (5, 0, 2)) (some (5, 0, 2)) (.next
      ([5010000000000], [990000000000]) (some (5, 0, 2)) (some (5, 0, 2)) (.next ([3000000000000],
      [990000000000]) (some (5, 0, 2)) (some (5, 0, 2)) (.next ([1485000000000], [885000000000])
      (some (5, 0, 2)) (some (5, 0, 2)) (.next ([2010000000000], [1260000000000]) (some (5, 0, 2))
      (some (5, 0, 3)) (.next ([4740000000000, 9000000000000], [3270000000000, -9000000000000])
      (some (5, 0, 3)) (some (5, 0, 3)) (.next ([3990000000000], [3000000000000]) (some (5, 0, 3))
      (some (5, 0, 3)) (.next ([3000000000000], [3000000000000]) (some (5, 0, 3)) (some (5, 0, 3))
      (.next ([2010000000000], [2250000000000]) (some (5, 0, 3)) (some (5, 0, 3)) (.next
      ([3750000000000], [4260000000000]) (some (5, 0, 3)) (some (5, 6, 3)) (.next ([1485000000000,
      9000000000000], [3885000000000, -9000000000000]) (some (5, 6, 3)) (some (5, 6, 3))
      fan48Owner3Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded48_5 : ExcludedOn (model48.B 5 ++ [step48.q]) 9000000000000 (model48.caps 5)
    (model48.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_6 : ExcludedOn (model48.B 6 ++ [step48.q]) 9000000000000 (model48.caps 6)
    (model48.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_7 : ExcludedOn (model48.B 7 ++ [step48.q]) 9000000000000 (model48.caps 7)
    (model48.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_8 : ExcludedOn (model48.B 8 ++ [step48.q]) 9000000000000 (model48.caps 8)
    (model48.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded48_3
    · exact (hj rfl).elim
    · exact excluded48_5
    · exact excluded48_6
    · exact excluded48_7
    · exact excluded48_8
    · exact excluded48_9
theorem next48 : model48.insert step48 = model49 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded49_0 : ExcludedOn (model49.B 0 ++ [step49.q]) 9000000000000 (model49.caps 0)
    (model49.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_1 : ExcludedOn (model49.B 1 ++ [step49.q]) 9000000000000 (model49.caps 1)
    (model49.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_3 : ExcludedOn (model49.B 3 ++ [step49.q]) 9000000000000 (model49.caps 3)
    (model49.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3495000000000], [390000000000]) (some (4, 0, 2))
      (some (5, 0, 2)) (.next ([4875000000000], [630000000000]) (some (5, 0, 2)) (some (5, 0, 6))
      (.next ([3885000000000], [630000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([5010000000000], [990000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([3000000000000],
      [990000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1485000000000], [885000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([3990000000000], [3000000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([3000000000000], [3000000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([4485000000000], [4515000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([3495000000000], [4515000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1485000000000,
      0], [2010000000000, -9000000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([1485000000000], [3000000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1485000000000,
      9000000000000], [3885000000000, -9000000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      fan49Owner3Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded49_4 : ExcludedOn (model49.B 4 ++ [step49.q]) 9000000000000 (model49.caps 4)
    (model49.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_5 : ExcludedOn (model49.B 5 ++ [step49.q]) 9000000000000 (model49.caps 5)
    (model49.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_6 : ExcludedOn (model49.B 6 ++ [step49.q]) 9000000000000 (model49.caps 6)
    (model49.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded49_0
    · exact excluded49_1
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_1 : ExcludedOn (model50.B 1 ++ [step50.q]) 9000000000000 (model50.caps 1)
    (model50.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_2 : ExcludedOn (model50.B 2 ++ [step50.q]) 9000000000000 (model50.caps 2)
    (model50.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5505000000000, 9000000000000], [495000000000,
      -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([4260000000000], [750000000000])
      (some (0, 6, 4)) (some (0, 6, 4)) (.next ([4140000000000], [960000000000]) (some (0, 6, 4))
      (some (0, 6, 4)) (.next ([2775000000000], [750000000000]) (some (0, 6, 4)) (some (0, 6, 4))
      (.next ([4515000000000], [1485000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
      ([2655000000000], [960000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([3000000000000],
      [1155000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([2370000000000], [1380000000000])
      (some (0, 6, 4)) (some (0, 6, 4)) (.next ([2460000000000], [1500000000000]) (some (0, 6, 4))
      (some (0, 6, 4)) (.next ([3000000000000], [2640000000000]) (some (0, 6, 4)) (some (0, 6, 4))
      (.next ([4350000000000, 9000000000000], [4650000000000, -9000000000000]) (some (0, 6, 4))
      (some (0, 6, 4)) (.next ([90000000000], [120000000000]) (some (0, 6, 4)) (some (0, 6, 4))
      (.next ([1980000000000, 9000000000000], [3270000000000, -9000000000000]) (some (0, 6, 4))
      (some (0, 6, 4)) fan50Owner2Part0)))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded50_4 : ExcludedOn (model50.B 4 ++ [step50.q]) 9000000000000 (model50.caps 4)
    (model50.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_5 : ExcludedOn (model50.B 5 ++ [step50.q]) 9000000000000 (model50.caps 5)
    (model50.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_6 : ExcludedOn (model50.B 6 ++ [step50.q]) 9000000000000 (model50.caps 6)
    (model50.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded50_4
    · exact excluded50_5
    · exact excluded50_6
    · exact excluded50_7
    · exact excluded50_8
    · exact excluded50_9
theorem next50 : model50.insert step50 = model51 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded51_0 : ExcludedOn (model51.B 0 ++ [step51.q]) 9000000000000 (model51.caps 0)
    (model51.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_1 : ExcludedOn (model51.B 1 ++ [step51.q]) 9000000000000 (model51.caps 1)
    (model51.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4380000000000, 9000000000000], [495000000000,
      -9000000000000]) (some (4, 4, 1)) (some (4, 4, 2)) (.next ([3390000000000], [1485000000000])
      (some (4, 4, 2)) (some (4, 4, 2)) (.next ([2400000000000, -9000000000000], [1485000000000, 0])
      (some (4, 4, 2)) (some (4, 4, 2)) (.next ([5490000000000, 9000000000000], [4590000000000,
      -9000000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([990000000000, 9000000000000],
      [990000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([4500000000000],
      [5580000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3510000000000, -9000000000000],
      [5580000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1110000000000],
      [4095000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0], [990000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-495000000000, 9000000000000], [4875000000000])
      (some (4, 1, 2)) (some (4, 1, 3)) (.next ([-1485000000000], [4875000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([-1485000000000, 0], [3885000000000, -9000000000000]) (some (4, 1,
      3)) (some (4, 1, 3)) (.next ([-4590000000000, 9000000000000], [10080000000000]) (some (4, 1,
      0)) (some (4, 1, 0)) (.next ([-990000000000, -9000000000000], [1980000000000, 18000000000000])
      (some (4, 1, 0)) (some (4, 1, 0)) (.next ([-5580000000000], [10080000000000]) (some (4, 1, 0))
      (some (4, 1, 0)) (.next ([-5580000000000, 0], [9090000000000, -9000000000000]) (some (4, 1,
      0)) (some (4, 1, 0)) (.next ([-4095000000000], [5205000000000]) (some (4, 1, 0)) (some (4, 1,
      0)) (.terminal (some (4, 1, 0)) (some (4, 1, 4)) (some (4, 1, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded51_3 : ExcludedOn (model51.B 3 ++ [step51.q]) 9000000000000 (model51.caps 3)
    (model51.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5640000000000], [360000000000]) (some (4, 0, 6))
      (some (5, 0, 6)) (.next ([4650000000000], [360000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([7920000000000], [1500000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([5010000000000], [990000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([6930000000000],
      [1500000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([3000000000000], [990000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([2280000000000], [1140000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([4500000000000, 0], [2430000000000, -9000000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([3990000000000], [3000000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([4500000000000], [3420000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([3000000000000], [3000000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      fan51Owner3Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded51_4 : ExcludedOn (model51.B 4 ++ [step51.q]) 9000000000000 (model51.caps 4)
    (model51.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_5 : ExcludedOn (model51.B 5 ++ [step51.q]) 9000000000000 (model51.caps 5)
    (model51.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_6 : ExcludedOn (model51.B 6 ++ [step51.q]) 9000000000000 (model51.caps 6)
    (model51.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_2 : ExcludedOn (model52.B 2 ++ [step52.q]) 9000000000000 (model52.caps 2)
    (model52.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_3 : ExcludedOn (model52.B 3 ++ [step52.q]) 9000000000000 (model52.caps 3)
    (model52.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5640000000000], [360000000000]) (some (4, 0, 6))
      (some (5, 0, 6)) (.next ([4650000000000], [360000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([5010000000000], [990000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([3000000000000], [990000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([3990000000000],
      [3000000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([3000000000000], [3000000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([3000000000000], [4200000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([990000000000], [1650000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([3000000000000], [5190000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([1800000000000], [4200000000000]) (some (5, 0, 6)) (some (5, 6, 6)) (.next ([810000000000],
      [2550000000000]) (some (5, 6, 3)) (some (5, 6, 3)) fan52Owner3Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded52_4 : ExcludedOn (model52.B 4 ++ [step52.q]) 9000000000000 (model52.caps 4)
    (model52.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5130000000000], [495000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) fan52Owner4Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded52_5 : ExcludedOn (model52.B 5 ++ [step52.q]) 9000000000000 (model52.caps 5)
    (model52.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8190000000000], [810000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([375000000000], [990000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([1365000000000], [6750000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([990000000000, 9000000000000], [7125000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([1065000000000], [7935000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([180000000000,
      9000000000000], [8010000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 4)) (.next ([0,
      0], [990000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-810000000000],
      [9000000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-990000000000], [1365000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-6750000000000], [8115000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-7125000000000, 0], [8115000000000, 9000000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-7935000000000], [9000000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-8010000000000, 9000000000000], [8190000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4))
      (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded52_6 : ExcludedOn (model52.B 6 ++ [step52.q]) 9000000000000 (model52.caps 6)
    (model52.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded53_0 : ExcludedOn (model53.B 0 ++ [step53.q]) 9000000000000 (model53.caps 0)
    (model53.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_2 : ExcludedOn (model53.B 2 ++ [step53.q]) 9000000000000 (model53.caps 2)
    (model53.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5505000000000, 9000000000000], [495000000000,
      -9000000000000]) (some (0, 0, 5)) (some (0, 1, 5)) fan53Owner2Part0)) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded53_3 : ExcludedOn (model53.B 3 ++ [step53.q]) 9000000000000 (model53.caps 3)
    (model53.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_4 : ExcludedOn (model53.B 4 ++ [step53.q]) 9000000000000 (model53.caps 4)
    (model53.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_5 : ExcludedOn (model53.B 5 ++ [step53.q]) 9000000000000 (model53.caps 5)
    (model53.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_6 : ExcludedOn (model53.B 6 ++ [step53.q]) 9000000000000 (model53.caps 6)
    (model53.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded53_0
    · exact (hj rfl).elim
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

theorem excluded54_1 : ExcludedOn (model54.B 1 ++ [step54.q]) 9000000000000 (model54.caps 1)
    (model54.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4380000000000, 9000000000000], [495000000000,
      -9000000000000]) (some (0, 5, 1)) (some (0, 5, 2)) (.next ([4950000000000, 9000000000000],
      [1050000000000, -9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([3390000000000],
      [1485000000000]) (some (0, 5, 2)) (some (0, 5, 2)) fan54Owner1Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_2 : ExcludedOn (model54.B 2 ++ [step54.q]) 9000000000000 (model54.caps 2)
    (model54.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_3 : ExcludedOn (model54.B 3 ++ [step54.q]) 9000000000000 (model54.caps 3)
    (model54.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_4 : ExcludedOn (model54.B 4 ++ [step54.q]) 9000000000000 (model54.caps 4)
    (model54.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_5 : ExcludedOn (model54.B 5 ++ [step54.q]) 9000000000000 (model54.caps 5)
    (model54.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_6 : ExcludedOn (model54.B 6 ++ [step54.q]) 9000000000000 (model54.caps 6)
    (model54.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3240000000000, 9000000000000], [330000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([2250000000000], [1320000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1320000000000], [4440000000000, -9000000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([990000000000, 9000000000000], [8010000000000,
      -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [990000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-330000000000, 9000000000000],
      [3570000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-1320000000000], [3570000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4440000000000, 9000000000000], [5760000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-8010000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_7 : ExcludedOn (model54.B 7 ++ [step54.q]) 9000000000000 (model54.caps 7)
    (model54.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_8 : ExcludedOn (model54.B 8 ++ [step54.q]) 9000000000000 (model54.caps 8)
    (model54.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_9 : ExcludedOn (model54.B 9 ++ [step54.q]) 9000000000000 (model54.caps 9)
    (model54.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked54 : StepValid model54 9000000000000 step54 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded54_1
    · exact excluded54_2
    · exact excluded54_3
    · exact excluded54_4
    · exact excluded54_5
    · exact excluded54_6
    · exact excluded54_7
    · exact excluded54_8
    · exact excluded54_9
theorem next54 : model54.insert step54 = model55 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext110000120000
end ConwaySoifer.Simplified.Certificates
