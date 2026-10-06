/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint170000180000
import Mathlib.Tactic.FinCases

/-!
# Sint 170000 180000 4

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
namespace Sint170000180000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner0Part0 : FanWitness := (.next ([990000000000], [6615000000000]) (some (0, 3, 6)) (some
    (0, 3, 6)) (.next ([1125000000000], [7875000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([885000000000], [6495000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([135000000000],
    [1260000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([615000000000], [7500000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([0], [1275000000000]) (some (0, 3, 6)) (some (0, 6,
    6)) (.next ([-225000000000], [4560000000000]) (some (0, 6, 6)) (some (0, 6, 6)) (.next
    ([-495000000000], [8115000000000]) (some (0, 6, 6)) (some (1, 6, 6)) (.next ([-510000000000],
    [6630000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-615000000000], [5325000000000])
    (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-1500000000000], [5835000000000]) (some (1, 6, 5))
    (some (1, 6, 5)) (.next ([-3165000000000], [9615000000000]) (some (1, 6, 5)) (some (1, 6, 5))
    (.next ([-2010000000000], [5460000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next
    ([-375000000000], [885000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-1170000000000],
    [2670000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-885000000000], [1785000000000])
    (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-390000000000], [765000000000]) (some (1, 6, 5))
    (some (1, 6, 5)) (.next ([-7500000000000], [9390000000000]) (some (1, 6, 5)) (some (2, 6, 5))
    (.next ([-5730000000000], [7005000000000]) (some (2, 6, 5)) (some (2, 6, 5)) (.next
    ([-6615000000000], [7605000000000]) (some (2, 6, 5)) (some (2, 6, 5)) (.next ([-7875000000000],
    [9000000000000]) (some (2, 6, 5)) (some (2, 6, 5)) (.next ([-6495000000000], [7380000000000])
    (some (2, 6, 5)) (some (2, 6, 5)) (.next ([-1260000000000], [1395000000000]) (some (2, 6, 5))
    (some (2, 6, 5)) (.next ([-7500000000000], [8115000000000]) (some (2, 6, 5)) (some (2, 6, 5))
    (.terminal (some (2, 6, 5)) (some (2, 6, 5)) (some (2, 6, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner6Part0 : FanWitness := (.next ([1350000000000, -9000000000000], [2025000000000,
    9000000000000]) (some (6, 2, 6)) (some (6, 2, 6)) (.next ([1335000000000, -9000000000000],
    [2040000000000, 9000000000000]) (some (6, 2, 6)) (some (6, 2, 6)) (.next ([2865000000000],
    [4635000000000]) (some (6, 2, 6)) (some (6, 2, 6)) (.next ([1035000000000, 9000000000000],
    [1845000000000, -9000000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([1020000000000,
    9000000000000], [1845000000000, -9000000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next
    ([1125000000000], [2040000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([2655000000000],
    [6375000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([1020000000000, 9000000000000],
    [7500000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([0], [15000000000]) (some (5, 2, 6))
    (some (5, 2, 6)) (.next ([-510000000000], [7500000000000]) (some (0, 2, 6)) (some (0, 3, 6))
    (.next ([-510000000000], [5970000000000, -9000000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([-405000000000, -9000000000000], [3570000000000, 9000000000000]) (some (0, 3, 6)) (some
    (0, 3, 6)) (.next ([-495000000000], [3375000000000]) (some (0, 3, 6)) (some (1, 3, 6)) (.next
    ([-510000000000], [3375000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-510000000000,
    9000000000000], [1635000000000, -9000000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next
    ([-1530000000000, -9000000000000], [3060000000000, 18000000000000]) (some (1, 3, 6)) (some (1,
    3, 6)) (.next ([-2025000000000, -9000000000000], [3375000000000]) (some (1, 3, 6)) (some (1, 3,
    6)) (.next ([-2040000000000, -9000000000000], [3375000000000]) (some (1, 3, 6)) (some (1, 3, 6))
    (.next ([-4635000000000], [7500000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next
    ([-1845000000000, 9000000000000], [2880000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next
    ([-1845000000000, 9000000000000], [2865000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next
    ([-2040000000000], [3165000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-6375000000000],
    [9030000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-7500000000000, 0], [8520000000000,
    9000000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.terminal (some (1, 3, 6)) (some (1, 3, 6))
    (some (1, 3, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner6Part1 : FanWitness := (.next ([2880000000000], [495000000000]) (some (6, 1, 6)) (some
    (6, 1, 6)) (.next ([2865000000000], [510000000000]) (some (6, 1, 6)) (some (6, 1, 6)) (.next
    ([1125000000000, 0], [510000000000, -9000000000000]) (some (6, 1, 6)) (some (6, 1, 6)) (.next
    ([1530000000000, 9000000000000], [1530000000000, 9000000000000]) (some (6, 1, 6)) (some (6, 2,
    6)) (.next ([1035000000000, 9000000000000], [1845000000000, -9000000000000]) (some (6, 2, 6))
    (some (6, 2, 6)) (.next ([1020000000000, 9000000000000], [1845000000000, -9000000000000]) (some
    (6, 2, 6)) (some (5, 2, 6)) (.next ([1125000000000], [2040000000000]) (some (5, 2, 6)) (some (5,
    2, 6)) (.next ([2655000000000], [6375000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next
    ([1020000000000, 9000000000000], [7500000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([0],
    [15000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([-510000000000], [7500000000000]) (some
    (0, 2, 6)) (some (0, 3, 6)) (.next ([-510000000000], [5970000000000, -9000000000000]) (some (0,
    3, 6)) (some (0, 3, 6)) (.next ([-210000000000], [1755000000000]) (some (0, 3, 6)) (some (0, 3,
    6)) (.next ([-210000000000], [1740000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-405000000000, -9000000000000], [3570000000000, 9000000000000]) (some (0, 3, 6)) (some (1, 3,
    6)) (.next ([-495000000000], [3375000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next
    ([-510000000000], [3375000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-510000000000,
    9000000000000], [1635000000000, -9000000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next
    ([-1530000000000, -9000000000000], [3060000000000, 18000000000000]) (some (1, 3, 6)) (some (1,
    3, 6)) (.next ([-1845000000000, 9000000000000], [2880000000000]) (some (1, 3, 6)) (some (1, 3,
    6)) (.next ([-1845000000000, 9000000000000], [2865000000000]) (some (1, 3, 6)) (some (1, 3, 6))
    (.next ([-2040000000000], [3165000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next
    ([-6375000000000], [9030000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-7500000000000,
    0], [8520000000000, 9000000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.terminal (some (1, 3,
    6)) (some (1, 3, 6)) (some (1, 3, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner0Part0 : FanWitness := (.next ([1275000000000], [5730000000000]) (some (6, 3, 5))
    (some (6, 3, 5)) (.next ([375000000000], [2520000000000]) (some (6, 3, 5)) (some (6, 3, 5))
    (.next ([885000000000], [6495000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([510000000000], [3780000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([135000000000],
    [1260000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([0], [1275000000000]) (some (6, 3,
    5)) (some (6, 3, 5)) (.next ([-225000000000], [4560000000000]) (some (6, 3, 5)) (some (6, 3, 5))
    (.next ([-510000000000], [6630000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-615000000000], [5325000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-390000000000],
    [2895000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-1500000000000], [5835000000000])
    (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-2010000000000], [5460000000000]) (some (6, 3, 5))
    (some (6, 3, 5)) (.next ([-375000000000], [885000000000]) (some (6, 3, 5)) (some (6, 3, 5))
    (.next ([-1170000000000], [2670000000000]) (some (6, 3, 5)) (some (6, 4, 5)) (.next
    ([-885000000000], [1785000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-390000000000],
    [765000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-6120000000000], [9900000000000])
    (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-4950000000000], [7230000000000]) (some (6, 4, 5))
    (some (6, 4, 5)) (.next ([-2895000000000], [3780000000000]) (some (6, 4, 5)) (some (6, 4, 5))
    (.next ([-5730000000000], [7005000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next
    ([-2520000000000], [2895000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-6495000000000],
    [7380000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-3780000000000], [4290000000000])
    (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-1260000000000], [1395000000000]) (some (6, 4, 5))
    (some (6, 4, 5)) (.terminal (some (6, 4, 5)) (some (6, 4, 5)) (some (6, 4,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner4Part0 : FanWitness := (.next ([5121000000000], [474000000000]) (some (4, 1, 5)) (some
    (4, 1, 5)) (.next ([5121000000000, 0], [1530000000000, 9000000000000]) (some (4, 1, 5)) (some
    (4, 1, 5)) (.next ([4065000000000, -9000000000000], [1530000000000, 9000000000000]) (some (4, 1,
    5)) (some (4, 1, 5)) (.next ([2220000000000], [2115000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([1440000000000], [1530000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([3750000000000], [4740000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2496000000000],
    [4155000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1530000000000], [2625000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2220000000000, -9000000000000], [4740000000000, 0])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([855000000000], [2895000000000]) (some (4, 1, 5))
    (some (4, 5, 5)) (.next ([381000000000], [8490000000000]) (some (4, 5, 3)) (some (4, 5, 3))
    (.next ([0, 0], [1530000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0,
    -9000000000000], [2625000000000, 0]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-474000000000],
    [5595000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1530000000000, -9000000000000],
    [6651000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next ([-1530000000000,
    -9000000000000], [5595000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2115000000000],
    [4335000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-1530000000000], [2970000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-4740000000000], [8490000000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.next ([-4155000000000], [6651000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-2625000000000], [4155000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-4740000000000, 0], [6960000000000, -9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-2895000000000], [3750000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-8490000000000],
    [8871000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5, 4)) (some (0, 5, 4))
    (some (0, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner6Part0 : FanWitness := (.next ([1530000000000], [210000000000]) (some (6, 6, 4)) (some
    (6, 6, 4)) (.next ([2880000000000], [495000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next
    ([2865000000000], [510000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next ([1125000000000, 0],
    [510000000000, -9000000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next ([5250000000000, 0],
    [2730000000000, -9000000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next ([4125000000000],
    [2220000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([5250000000000], [4260000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([1530000000000, 9000000000000], [1530000000000,
    9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([2385000000000], [3750000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([2370000000000], [3765000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([1125000000000], [2040000000000]) (some (6, 2, 4)) (some (6, 2, 4))
    (.next ([0], [15000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-210000000000],
    [1755000000000]) (some (6, 2, 4)) (some (6, 3, 4)) (.next ([-210000000000], [1740000000000])
    (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-495000000000], [3375000000000]) (some (6, 3, 4))
    (some (6, 3, 4)) (.next ([-510000000000], [3375000000000]) (some (6, 3, 4)) (some (6, 3, 4))
    (.next ([-510000000000, 9000000000000], [1635000000000, -9000000000000]) (some (6, 3, 4)) (some
    (6, 3, 4)) (.next ([-2730000000000, 9000000000000], [7980000000000, -9000000000000]) (some (6,
    3, 4)) (some (6, 3, 4)) (.next ([-2220000000000], [6345000000000]) (some (6, 3, 4)) (some (6, 3,
    4)) (.next ([-4260000000000], [9510000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-1530000000000, -9000000000000], [3060000000000, 18000000000000]) (some (6, 3, 4)) (some (6,
    3, 4)) (.next ([-3750000000000], [6135000000000]) (some (6, 3, 4)) (some (6, 3, 5)) (.next
    ([-3765000000000], [6135000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-2040000000000],
    [3165000000000]) (some (6, 3, 5)) (some (6, 3, 6)) (.terminal (some (6, 3, 6)) (some (6, 3, 6))
    (some (6, 3, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan38Owner3Part0 : FanWitness := (.next ([6246000000000], [1284000000000, 9000000000000]) (some
    (4, 0, 5)) (some (4, 1, 5)) (.next ([2379000000000], [555000000000]) (some (4, 1, 5)) (some (4,
    1, 5)) (.next ([6345000000000], [1530000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1,
    5)) (.next ([5736000000000], [1764000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([1500000000000], [510000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([5835000000000],
    [2010000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([99000000000], [246000000000]) (some
    (4, 1, 5)) (some (4, 1, 5)) (.next ([2625000000000], [6555000000000]) (some (4, 1, 5)) (some (4,
    1, 5)) (.next ([1095000000000, -9000000000000], [8085000000000, 9000000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([615000000000], [8055000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([246000000000], [6000000000000]) (some (4, 1, 5)) (some (4, 5, 5)) (.next ([0],
    [1530000000000, 9000000000000]) (some (4, 5, 5)) (some (4, 5, 5)) (.next ([-210000000000],
    [2835000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-1284000000000, -9000000000000],
    [7530000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-555000000000],
    [2934000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1530000000000, -9000000000000],
    [7875000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1764000000000],
    [7500000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-510000000000], [2010000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2010000000000], [7845000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-246000000000], [345000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-6555000000000], [9180000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-8085000000000, -9000000000000], [9180000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-8055000000000], [8670000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-6000000000000],
    [6246000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3)) (some (0, 5, 3))
    (some (0, 5, 3)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4335000000000], [225000000000]) (some (5, 2, 6))
      (some (5, 2, 6)) (.next ([7620000000000], [495000000000]) (some (5, 2, 6)) (some (5, 2, 6))
      (.next ([6120000000000], [510000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next
      ([4710000000000], [615000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([4335000000000],
      [1500000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([6450000000000], [3165000000000])
      (some (5, 2, 6)) (some (5, 2, 6)) (.next ([3450000000000], [2010000000000]) (some (5, 2, 6))
      (some (5, 2, 6)) (.next ([510000000000], [375000000000]) (some (5, 2, 6)) (some (5, 2, 6))
      (.next ([1500000000000], [1170000000000]) (some (5, 2, 6)) (some (5, 3, 6)) (.next
      ([900000000000], [885000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([375000000000],
      [390000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([1890000000000], [7500000000000])
      (some (0, 3, 6)) (some (0, 3, 6)) (.next ([1275000000000], [5730000000000]) (some (0, 3, 6))
      (some (0, 3, 6)) fan32Owner0Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_5 : ExcludedOn (model32.B 5 ++ [step32.q]) 9000000000000 (model32.caps 5)
    (model32.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_6 : ExcludedOn (model32.B 6 ++ [step32.q]) 9000000000000 (model32.caps 6)
    (model32.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (61) (120) (12000) (.witnessedFan (.next ([6990000000000],
      [510000000000]) (some (6, 1, 3)) (some (6, 1, 4)) (.next ([5460000000000, -9000000000000],
      [510000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3165000000000], [405000000000,
      9000000000000]) (some (6, 1, 4)) (some (6, 1, 6)) (.next ([2880000000000], [495000000000])
      (some (6, 1, 6)) (some (6, 1, 6)) (.next ([2865000000000], [510000000000]) (some (6, 1, 6))
      (some (6, 1, 6)) (.next ([1125000000000, 0], [510000000000, -9000000000000]) (some (6, 1, 6))
      (some (6, 1, 6)) (.next ([1530000000000, 9000000000000], [1530000000000, 9000000000000]) (some
      (6, 1, 6)) (some (6, 2, 6)) fan32Owner6Part0)))))))) (.witnessedFan (.next ([6990000000000],
      [510000000000]) (some (6, 1, 3)) (some (6, 1, 4)) (.next ([5460000000000, -9000000000000],
      [510000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([1545000000000], [210000000000])
      (some (6, 1, 4)) (some (6, 1, 6)) (.next ([1530000000000], [210000000000]) (some (6, 1, 6))
      (some (6, 1, 6)) (.next ([3165000000000], [405000000000, 9000000000000]) (some (6, 1, 6))
      (some (6, 1, 6)) fan32Owner6Part1))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0
      1 100 (by decide +kernel)
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

theorem excluded32_9 : ExcludedOn (model32.B 9 ++ [step32.q]) 9000000000000 (model32.caps 9)
    (model32.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded32_2
    · exact excluded32_3
    · exact excluded32_4
    · exact excluded32_5
    · exact excluded32_6
    · exact excluded32_7
    · exact excluded32_8
    · exact excluded32_9
theorem next32 : model32.insert step32 = model33 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded33_0 : ExcludedOn (model33.B 0 ++ [step33.q]) 9000000000000 (model33.caps 0)
    (model33.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_1 : ExcludedOn (model33.B 1 ++ [step33.q]) 9000000000000 (model33.caps 1)
    (model33.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_2 : ExcludedOn (model33.B 2 ++ [step33.q]) 9000000000000 (model33.caps 2)
    (model33.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_3 : ExcludedOn (model33.B 3 ++ [step33.q]) 9000000000000 (model33.caps 3)
    (model33.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_4 : ExcludedOn (model33.B 4 ++ [step33.q]) 9000000000000 (model33.caps 4)
    (model33.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4611000000000], [264000000000]) (some (3, 0, 2))
      (some (3, 4, 2)) (.next ([4875000000000], [510000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([5121000000000, 0], [1530000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([3345000000000, -9000000000000], [2040000000000, 9000000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([5121000000000], [3654000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([1221000000000], [4164000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0, 0],
      [1530000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-264000000000],
      [4875000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-510000000000], [5385000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-1530000000000, -9000000000000], [6651000000000,
      9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-2040000000000, -9000000000000],
      [5385000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3654000000000],
      [8775000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-4164000000000], [5385000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 2, 3)) (some (0, 2, 3)) (some (0, 2,
      3))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded33_4
    · exact (hj rfl).elim
    · exact excluded33_6
    · exact excluded33_7
    · exact excluded33_8
    · exact excluded33_9
theorem next33 : model33.insert step33 = model34 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded34_0 : ExcludedOn (model34.B 0 ++ [step34.q]) 9000000000000 (model34.caps 0)
    (model34.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_1 : ExcludedOn (model34.B 1 ++ [step34.q]) 9000000000000 (model34.caps 1)
    (model34.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_3 : ExcludedOn (model34.B 3 ++ [step34.q]) 9000000000000 (model34.caps 3)
    (model34.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4500000000000], [510000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([5346000000000, 0], [1530000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([2970000000000, -9000000000000], [2040000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2460000000000], [1875000000000]) (some (4, 1, 2))
      (some (4, 1, 3)) (.next ([2625000000000], [4845000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([501000000000], [2124000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([1095000000000, -9000000000000], [6375000000000, 9000000000000]) (some (0, 1, 3)) (some (0,
      1, 3)) (.next ([336000000000], [4500000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [5346000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-510000000000], [5010000000000])
      (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-1530000000000, -9000000000000], [6876000000000,
      9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2040000000000, -9000000000000],
      [5010000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1875000000000], [4335000000000])
      (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-4845000000000], [7470000000000]) (some (0, 2, 3))
      (some (0, 2, 4)) (.next ([-2124000000000], [2625000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-6375000000000, -9000000000000], [7470000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-4500000000000], [4836000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded34_0
    · exact excluded34_1
    · exact excluded34_2
    · exact excluded34_3
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4335000000000], [225000000000]) (some (5, 6, 4))
      (some (5, 6, 4)) (.next ([6120000000000], [510000000000]) (some (5, 6, 4)) (some (5, 6, 4))
      (.next ([4710000000000], [615000000000]) (some (5, 6, 4)) (some (5, 6, 5)) (.next
      ([2505000000000], [390000000000]) (some (5, 6, 5)) (some (5, 6, 5)) (.next ([4335000000000],
      [1500000000000]) (some (5, 6, 5)) (some (5, 6, 5)) (.next ([3450000000000], [2010000000000])
      (some (5, 6, 5)) (some (5, 6, 5)) (.next ([510000000000], [375000000000]) (some (5, 6, 5))
      (some (5, 6, 5)) (.next ([1500000000000], [1170000000000]) (some (5, 6, 5)) (some (5, 6, 5))
      (.next ([900000000000], [885000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
      ([375000000000], [390000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([3780000000000],
      [6120000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([2280000000000], [4950000000000])
      (some (0, 6, 5)) (some (0, 6, 5)) (.next ([885000000000], [2895000000000]) (some (0, 6, 5))
      (some (6, 6, 5)) fan35Owner0Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_1 : ExcludedOn (model35.B 1 ++ [step35.q]) 9000000000000 (model35.caps 1)
    (model35.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_2 : ExcludedOn (model35.B 2 ++ [step35.q]) 9000000000000 (model35.caps 2)
    (model35.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_3 : ExcludedOn (model35.B 3 ++ [step35.q]) 9000000000000 (model35.caps 3)
    (model35.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_5 : ExcludedOn (model35.B 5 ++ [step35.q]) 9000000000000 (model35.caps 5)
    (model35.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4500000000000], [510000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([5346000000000, 0], [1530000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([5595000000000], [3405000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([2970000000000, -9000000000000], [2040000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([4065000000000, -9000000000000], [4935000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 3)) (.next ([1941000000000], [3654000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([1095000000000], [2895000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([336000000000], [4500000000000]) (some (0, 1, 3)) (some (0, 1, 4)) (.next ([0],
      [5346000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-510000000000], [5010000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1530000000000, -9000000000000], [6876000000000,
      9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-3405000000000], [9000000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2040000000000, -9000000000000], [5010000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4935000000000, -9000000000000], [9000000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-3654000000000], [5595000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2895000000000], [3990000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-4500000000000], [4836000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_6 : ExcludedOn (model35.B 6 ++ [step35.q]) 9000000000000 (model35.caps 6)
    (model35.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded35_5
    · exact excluded35_6
    · exact excluded35_7
    · exact excluded35_8
    · exact excluded35_9
theorem next35 : model35.insert step35 = model36 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded36_1 : ExcludedOn (model36.B 1 ++ [step36.q]) 9000000000000 (model36.caps 1)
    (model36.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_2 : ExcludedOn (model36.B 2 ++ [step36.q]) 9000000000000 (model36.caps 2)
    (model36.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3720000000000, -9000000000000], [0,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([7470000000000, -9000000000000],
      [1530000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([3750000000000,
      -9000000000000], [5250000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([1530000000000], [3720000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0],
      [1530000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, -9000000000000],
      [3720000000000]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-1530000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (3, 1, 2)) (.next ([-5250000000000, 0],
      [9000000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3720000000000],
      [5250000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_3 : ExcludedOn (model36.B 3 ++ [step36.q]) 9000000000000 (model36.caps 3)
    (model36.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([480000000000, -9000000000000], [30000000000,
      9000000000000]) (some (3, 0, 5)) (some (4, 0, 5)) (.next ([1500000000000], [510000000000])
      (some (4, 0, 5)) (some (4, 1, 5)) (.next ([5835000000000], [2010000000000]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([2595000000000], [1125000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([2250000000000], [1224000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([3720000000000], [3750000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([2190000000000,
      -9000000000000], [5280000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([1710000000000], [5250000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([246000000000],
      [6000000000000]) (some (4, 1, 3)) (some (4, 5, 3)) (.next ([0], [1530000000000,
      9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([-30000000000, -9000000000000],
      [510000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-510000000000], [2010000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2010000000000], [7845000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-1125000000000], [3720000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-1224000000000], [3474000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-3750000000000], [7470000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-5280000000000,
      -9000000000000], [7470000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-5250000000000],
      [6960000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-6000000000000], [6246000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5,
      3))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded36_4 : ExcludedOn (model36.B 4 ++ [step36.q]) 9000000000000 (model36.caps 4)
    (model36.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_6 : ExcludedOn (model36.B 6 ++ [step36.q]) 9000000000000 (model36.caps 6)
    (model36.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded36_9 : ExcludedOn (model36.B 9 ++ [step36.q]) 9000000000000 (model36.caps 9)
    (model36.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked36 : StepValid model36 9000000000000 step36 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded36_1
    · exact excluded36_2
    · exact excluded36_3
    · exact excluded36_4
    · exact excluded36_5
    · exact excluded36_6
    · exact excluded36_7
    · exact excluded36_8
    · exact excluded36_9
theorem next36 : model36.insert step36 = model37 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded37_0 : ExcludedOn (model37.B 0 ++ [step37.q]) 9000000000000 (model37.caps 0)
    (model37.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_1 : ExcludedOn (model37.B 1 ++ [step37.q]) 9000000000000 (model37.caps 1)
    (model37.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([2625000000000, -9000000000000], [0,
      9000000000000]) (some (4, 0, 5)) (some (4, 1, 5)) fan37Owner4Part0)) (den := 9000000000000)
      (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_6 : ExcludedOn (model37.B 6 ++ [step37.q]) 9000000000000 (model37.caps 6)
    (model37.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1545000000000], [210000000000]) (some (6, 6, 3))
      (some (6, 6, 4)) fan37Owner6Part0)) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded37_6
    · exact excluded37_7
    · exact excluded37_8
    · exact excluded37_9
theorem next37 : model37.insert step37 = model38 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded38_1 : ExcludedOn (model38.B 1 ++ [step38.q]) 9000000000000 (model38.caps 1)
    (model38.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7875000000000], [435000000000]) none none (.next
      ([7905000000000, 9000000000000], [915000000000, -9000000000000]) none none (.next
      ([6375000000000], [2445000000000]) none none (.next ([4845000000000, -9000000000000],
      [2445000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([2010000000000, 0],
      [1020000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1530000000000,
      9000000000000], [1530000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([510000000000], [1500000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([30000000000,
      9000000000000], [480000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0,
      0], [1530000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 2, 3)) (.next ([-435000000000],
      [8310000000000]) (some (4, 2, 0)) (some (4, 2, 0)) (.next ([-915000000000, 9000000000000],
      [8820000000000]) (some (4, 2, 0)) (some (4, 2, 0)) (.next ([-2445000000000], [8820000000000])
      (some (4, 2, 0)) (some (4, 2, 0)) (.next ([-2445000000000, 0], [7290000000000,
      -9000000000000]) (some (4, 2, 0)) (some (4, 2, 0)) (.next ([-1020000000000, -9000000000000],
      [3030000000000, 9000000000000]) (some (4, 2, 0)) (some (4, 2, 4)) (.next ([-1530000000000,
      -9000000000000], [3060000000000, 18000000000000]) (some (4, 2, 4)) (some (4, 2, 4)) (.next
      ([-1500000000000], [2010000000000]) (some (4, 2, 4)) (some (4, 2, 4)) (.next ([-480000000000,
      9000000000000], [510000000000]) (some (4, 2, 4)) (some (4, 2, 4)) (.terminal (some (4, 2, 4))
      none none))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded38_2 : ExcludedOn (model38.B 2 ++ [step38.q]) 9000000000000 (model38.caps 2)
    (model38.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2445000000000], [180000000000]) (some (0, 3, 1))
      (some (0, 3, 1)) (.next ([7470000000000, -9000000000000], [1530000000000, 9000000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4845000000000, -9000000000000], [2445000000000, 0])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([915000000000, -9000000000000], [1710000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [1530000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-180000000000], [2625000000000])
      (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-1530000000000, -9000000000000], [9000000000000,
      0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2445000000000, 0], [7290000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1710000000000, -9000000000000],
      [2625000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_3 : ExcludedOn (model38.B 3 ++ [step38.q]) 9000000000000 (model38.caps 3)
    (model38.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2625000000000], [210000000000]) (some (3, 0, 5))
      (some (4, 0, 5)) fan38Owner3Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded38_4 : ExcludedOn (model38.B 4 ++ [step38.q]) 9000000000000 (model38.caps 4)
    (model38.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_5 : ExcludedOn (model38.B 5 ++ [step38.q]) 9000000000000 (model38.caps 5)
    (model38.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_6 : ExcludedOn (model38.B 6 ++ [step38.q]) 9000000000000 (model38.caps 6)
    (model38.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_7 : ExcludedOn (model38.B 7 ++ [step38.q]) 9000000000000 (model38.caps 7)
    (model38.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_8 : ExcludedOn (model38.B 8 ++ [step38.q]) 9000000000000 (model38.caps 8)
    (model38.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_9 : ExcludedOn (model38.B 9 ++ [step38.q]) 9000000000000 (model38.caps 9)
    (model38.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked38 : StepValid model38 9000000000000 step38 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded38_1
    · exact excluded38_2
    · exact excluded38_3
    · exact excluded38_4
    · exact excluded38_5
    · exact excluded38_6
    · exact excluded38_7
    · exact excluded38_8
    · exact excluded38_9
theorem next38 : model38.insert step38 = model39 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded39_0 : ExcludedOn (model39.B 0 ++ [step39.q]) 9000000000000 (model39.caps 0)
    (model39.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_1 : ExcludedOn (model39.B 1 ++ [step39.q]) 9000000000000 (model39.caps 1)
    (model39.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_5 : ExcludedOn (model39.B 5 ++ [step39.q]) 9000000000000 (model39.caps 5)
    (model39.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_6 : ExcludedOn (model39.B 6 ++ [step39.q]) 9000000000000 (model39.caps 6)
    (model39.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded39_6
    · exact excluded39_7
    · exact excluded39_8
    · exact (hj rfl).elim
theorem next39 : model39.insert step39 = model40 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint170000180000
end ConwaySoifer.Simplified.Certificates
