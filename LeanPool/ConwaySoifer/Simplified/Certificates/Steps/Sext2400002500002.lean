/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext240000250000
import Mathlib.Tactic.FinCases

/-!
# Sext 240000 250000 2

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
namespace Sext240000250000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan16Owner0Part0 : FanWitness := (.next ([-1125000000000], [5970000000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-1470000000000], [7275000000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-1485000000000], [6720000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1485000000000], [6405000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1440000000000], [5970000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1125000000000], [4125000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1875000000000], [6870000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1875000000000], [6555000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1440000000000], [4440000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1845000000000], [5565000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1845000000000], [5250000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-810000000000],
    [2250000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-405000000000], [810000000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-5205000000000], [10125000000000]) (some (10, 3,
    6)) (some (10, 3, 7)) (.next ([-5595000000000], [10275000000000]) (some (10, 3, 7)) (some (10,
    3, 7)) (.next ([-240000000000], [390000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next
    ([-720000000000], [1125000000000]) (some (10, 3, 7)) (some (10, 4, 7)) (.next ([-1530000000000],
    [1845000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next ([-5280000000000], [6045000000000])
    (some (10, 4, 7)) (some (10, 4, 7)) (.next ([-5595000000000], [6360000000000]) (some (10, 4, 7))
    (some (10, 4, 7)) (.next ([-5430000000000], [5805000000000]) (some (10, 4, 7)) (some (10, 4, 7))
    (.next ([-5745000000000], [6120000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-6405000000000], [6765000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-6720000000000], [6765000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.terminal (some (10, 4,
    7)) (some (10, 4, 7)) (some (10, 4, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan16Owner0Part1 : FanWitness := (.next ([3000000000000], [1440000000000]) (some (8, 10, 4))
    (some (8, 10, 4)) (.next ([3720000000000], [1845000000000]) (some (8, 10, 4)) (some (8, 10, 4))
    (.next ([3405000000000], [1845000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
    ([1440000000000], [810000000000]) (some (8, 10, 4)) (some (10, 10, 4)) (.next ([405000000000],
    [405000000000]) (some (10, 10, 4)) (some (10, 10, 4)) (.next ([4920000000000], [5205000000000])
    (some (10, 10, 4)) (some (10, 10, 4)) (.next ([4680000000000], [5595000000000]) (some (10, 3,
    4)) (some (10, 3, 4)) (.next ([150000000000], [240000000000]) (some (10, 3, 4)) (some (10, 3,
    4)) (.next ([405000000000], [720000000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next
    ([315000000000], [1530000000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([765000000000],
    [5280000000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([765000000000], [5595000000000])
    (some (10, 3, 4)) (some (10, 3, 4)) (.next ([375000000000], [5430000000000]) (some (10, 3, 4))
    (some (10, 3, 4)) (.next ([375000000000], [5745000000000]) (some (10, 3, 4)) (some (10, 3, 5))
    (.next ([360000000000], [6405000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
    ([45000000000], [6720000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([0],
    [1845000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-30000000000], [6555000000000])
    (some (10, 3, 5)) (some (10, 3, 6)) (.next ([-345000000000], [6870000000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-315000000000], [3720000000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-765000000000], [7125000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1080000000000], [7125000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1155000000000], [7275000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-315000000000],
    [1845000000000]) (some (10, 3, 6)) (some (10, 3, 6)) fan16Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner4Part0 : FanWitness := (.next ([2880000000000, 9000000000000], [1995000000000,
    -9000000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next ([2520000000000, 9000000000000],
    [2340000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2160000000000,
    9000000000000], [4215000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([750000000000],
    [2160000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([915000000000],
    [4125000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([660000000000], [3495000000000])
    (some (4, 1, 3)) (some (4, 1, 3)) (.next ([750000000000], [4320000000000]) (some (4, 1, 3))
    (some (4, 1, 3)) (.next ([720000000000], [4155000000000]) (some (4, 1, 3)) (some (4, 1, 3))
    (.next ([645000000000], [3855000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
    ([570000000000], [4110000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([360000000000],
    [4500000000000]) (some (4, 1, 3)) (some (4, 1, 5)) (.next ([0], [4215000000000]) (some (4, 1,
    5)) (some (4, 1, 5)) (.next ([-15000000000], [360000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-1995000000000, 9000000000000], [4875000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-2340000000000, 9000000000000], [4860000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-4215000000000], [6375000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-2160000000000, 9000000000000], [2910000000000, -9000000000000]) (some (0, 1, 5)) (some
    (0, 1, 5)) (.next ([-4125000000000], [5040000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-3495000000000], [4155000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4320000000000],
    [5070000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-4155000000000], [4875000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3855000000000], [4500000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-4110000000000], [4680000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-4500000000000], [4860000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some
    (0, 2, 5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner4Part0 : FanWitness := (.next ([5040000000000], [3300000000000]) (some (5, 1, 2))
    (some (5, 1, 3)) (.next ([2520000000000, 9000000000000], [2340000000000, -9000000000000]) (some
    (5, 1, 3)) (some (5, 1, 3)) (.next ([2160000000000, 9000000000000], [4215000000000]) (some (5,
    1, 3)) (some (5, 1, 3)) (.next ([915000000000], [1965000000000, -9000000000000]) (some (5, 1,
    3)) (some (5, 1, 3)) (.next ([885000000000], [3960000000000]) (some (4, 1, 3)) (some (4, 1, 3))
    (.next ([915000000000], [4125000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
    ([660000000000], [3495000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([720000000000],
    [4155000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([645000000000], [3855000000000])
    (some (4, 1, 3)) (some (4, 1, 3)) (.next ([540000000000], [3945000000000]) (some (4, 1, 3))
    (some (4, 1, 3)) (.next ([360000000000], [4500000000000]) (some (4, 1, 3)) (some (4, 1, 5))
    (.next ([0], [4215000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([-15000000000],
    [360000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3300000000000], [8340000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2340000000000, 9000000000000], [4860000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4215000000000], [6375000000000, 9000000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1965000000000, 9000000000000], [2880000000000,
    -9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3960000000000], [4845000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4125000000000], [5040000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-3495000000000], [4155000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-4155000000000], [4875000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
    ([-3855000000000], [4500000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3945000000000],
    [4485000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4500000000000], [4860000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner4Part0 : FanWitness := (.next ([4320000000000], [2052000000000, -9000000000000]) (some
    (5, 1, 3)) (some (5, 1, 5)) (.next ([2880000000000, 9000000000000], [1995000000000,
    -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2520000000000, 9000000000000],
    [2340000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([4320000000000],
    [4212000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2160000000000, 9000000000000],
    [4215000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([660000000000], [3495000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([720000000000], [4155000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([645000000000], [3855000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([360000000000], [4500000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([105000000000], [8427000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0],
    [4215000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([-15000000000], [360000000000]) (some
    (0, 1, 5)) (some (0, 1, 5)) (.next ([-555000000000], [4932000000000]) (some (0, 1, 5)) (some (0,
    1, 5)) (.next ([-540000000000], [4572000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-2052000000000, 9000000000000], [6372000000000, -9000000000000]) (some (0, 1, 5)) (some (0, 1,
    5)) (.next ([-1995000000000, 9000000000000], [4875000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-2340000000000, 9000000000000], [4860000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-4212000000000], [8532000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-4215000000000], [6375000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-3495000000000], [4155000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4155000000000],
    [4875000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-3855000000000], [4500000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4500000000000], [4860000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-8427000000000], [8532000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner0Part0 : FanWitness := (.next ([-1470000000000], [7275000000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-1485000000000], [6720000000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-1485000000000], [6405000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1875000000000], [6870000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1875000000000], [6555000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-810000000000],
    [2250000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-405000000000], [810000000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-240000000000], [390000000000]) (some (10, 3, 6))
    (some (10, 3, 7)) (.next ([-720000000000], [1125000000000]) (some (10, 3, 7)) (some (10, 4, 7))
    (.next ([-6780000000000], [9405000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-7095000000000], [9405000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-5655000000000], [7155000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-1530000000000], [1845000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-7500000000000], [9000000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-5970000000000], [7155000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-7500000000000], [8685000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-5280000000000], [6045000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-5595000000000], [6360000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-6780000000000], [7560000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-7095000000000], [7875000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-5430000000000], [5805000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-5745000000000], [6120000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-6405000000000], [6765000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-6720000000000], [6765000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.terminal (some (10, 4,
    7)) (some (10, 4, 7)) (some (10, 4, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner0Part1 : FanWitness := (.next ([2625000000000], [6780000000000]) (some (9, 10, 4))
    (some (9, 10, 4)) (.next ([2310000000000], [7095000000000]) (some (9, 10, 4)) (some (9, 10, 4))
    (.next ([1500000000000], [5655000000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next
    ([315000000000], [1530000000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next ([1500000000000],
    [7500000000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next ([1185000000000], [5970000000000])
    (some (9, 10, 4)) (some (9, 10, 4)) (.next ([1185000000000], [7500000000000]) (some (9, 10, 4))
    (some (9, 10, 4)) (.next ([765000000000], [5280000000000]) (some (9, 10, 4)) (some (9, 10, 4))
    (.next ([765000000000], [5595000000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next
    ([780000000000], [6780000000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next ([780000000000],
    [7095000000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next ([375000000000], [5430000000000])
    (some (9, 10, 4)) (some (10, 10, 4)) (.next ([375000000000], [5745000000000]) (some (10, 10, 4))
    (some (10, 10, 5)) (.next ([360000000000], [6405000000000]) (some (10, 10, 5)) (some (10, 10,
    5)) (.next ([45000000000], [6720000000000]) (some (10, 10, 5)) (some (10, 10, 5)) (.next ([0],
    [1845000000000]) (some (10, 10, 5)) (some (10, 10, 5)) (.next ([-30000000000], [6555000000000])
    (some (10, 10, 5)) (some (10, 10, 6)) (.next ([-345000000000], [6870000000000]) (some (10, 10,
    6)) (some (10, 10, 6)) (.next ([-735000000000], [8640000000000]) (some (10, 10, 6)) (some (10,
    10, 6)) (.next ([-765000000000], [7125000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-975000000000], [9030000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-1080000000000],
    [7125000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-1155000000000], [7275000000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-315000000000], [1845000000000]) (some (10, 3, 6))
    (some (10, 3, 6)) fan22Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner4Part0 : FanWitness := (.next ([6375000000000], [720000000000]) (some (4, 1, 5)) (some
    (4, 1, 5)) (.next ([2160000000000], [720000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([3780000000000], [2235000000000]) (some (4, 1, 5)) (some (4, 5, 5)) (.next ([3435000000000],
    [2220000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([2520000000000, 9000000000000],
    [2340000000000, -9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([2160000000000,
    9000000000000], [4215000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([1440000000000,
    9000000000000], [7095000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([660000000000],
    [3495000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([720000000000], [4155000000000])
    (some (4, 5, 3)) (some (4, 5, 3)) (.next ([645000000000], [3855000000000]) (some (4, 5, 3))
    (some (4, 5, 3)) (.next ([360000000000], [4500000000000]) (some (4, 5, 3)) (some (4, 5, 3))
    (.next ([0], [4215000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([-15000000000],
    [360000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-720000000000], [7095000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-720000000000], [2880000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-2235000000000], [6015000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-2220000000000], [5655000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-2340000000000, 9000000000000], [4860000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-4215000000000], [6375000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next
    ([-7095000000000], [8535000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-3495000000000], [4155000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-4155000000000],
    [4875000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3855000000000], [4500000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-4500000000000], [4860000000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.terminal (some (0, 5, 4)) (some (0, 5, 4)) (some (0, 5,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner3Part0 : FanWitness := (.next ([2160000000000, 9000000000000], [2655000000000,
    -9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([1410000000000, 9000000000000],
    [4680000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([1245000000000, 9000000000000],
    [4875000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([30000000000], [165000000000]) (some
    (6, 2, 4)) (some (6, 2, 4)) (.next ([468000000000], [4320000000000]) (some (6, 2, 4)) (some (6,
    2, 4)) (.next ([108000000000], [3462000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([0],
    [2160000000000, 9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-87000000000],
    [3492000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-855000000000], [5730000000000])
    (some (6, 2, 4)) (some (6, 3, 4)) (.next ([-885000000000], [5565000000000]) (some (6, 3, 4))
    (some (6, 3, 4)) (.next ([-750000000000], [4680000000000]) (some (6, 3, 4)) (some (6, 3, 4))
    (.next ([-915000000000], [4875000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-750000000000], [2520000000000, -9000000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-915000000000], [2715000000000, -9000000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-1692000000000, -9000000000000], [4320000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-2160000000000, 9000000000000], [4788000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-4347000000000], [9135000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-2160000000000,
    -9000000000000], [4320000000000, 18000000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-2655000000000, 9000000000000], [4815000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-4680000000000, 0], [6090000000000, 9000000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-4875000000000, 0], [6120000000000, 9000000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-165000000000], [195000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-4320000000000],
    [4788000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-3462000000000], [3570000000000])
    (some (6, 3, 4)) (some (6, 3, 4)) (.terminal (some (6, 3, 4)) (some (6, 3, 4)) (some (6, 3,
    4)))))))))))))))))))))))))))

theorem excluded16_0 : ExcludedOn (model16.B 0 ++ [step16.q]) 9000000000000 (model16.caps 0)
    (model16.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6525000000000], [30000000000]) (some (7, 10, 4))
      (some (8, 10, 4)) (.next ([6525000000000], [345000000000]) (some (8, 10, 4)) (some (8, 10, 4))
      (.next ([3405000000000], [315000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([6360000000000], [765000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([6045000000000],
      [1080000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([6120000000000], [1155000000000])
      (some (8, 10, 4)) (some (8, 10, 4)) (.next ([1530000000000], [315000000000]) (some (8, 10, 4))
      (some (8, 10, 4)) (.next ([4845000000000], [1125000000000]) (some (8, 10, 4)) (some (8, 10,
      4)) (.next ([5805000000000], [1470000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([5235000000000], [1485000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([4920000000000], [1485000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([4530000000000], [1440000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([3000000000000], [1125000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([4995000000000], [1875000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([4680000000000], [1875000000000]) (some (8, 10, 4)) (some (8, 10, 4))
      fan16Owner0Part1)))))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_1 : ExcludedOn (model16.B 1 ++ [step16.q]) 9000000000000 (model16.caps 1)
    (model16.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_2 : ExcludedOn (model16.B 2 ++ [step16.q]) 9000000000000 (model16.caps 2)
    (model16.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_3 : ExcludedOn (model16.B 3 ++ [step16.q]) 9000000000000 (model16.caps 3)
    (model16.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7005000000000, 9000000000000], [2715000000000,
      -9000000000000]) (some (1, 3, 3)) (some (2, 3, 3)) (.next ([2160000000000, 9000000000000],
      [2160000000000, 9000000000000]) (some (2, 3, 1)) (some (2, 3, 1)) (.next ([4845000000000],
      [4875000000000]) (some (2, 3, 1)) (some (2, 3, 1)) (.next ([2685000000000, -9000000000000],
      [4875000000000]) (some (2, 3, 1)) (some (2, 3, 1)) (.next ([0], [2160000000000,
      9000000000000]) (some (2, 3, 1)) (some (2, 3, 1)) (.next ([-2715000000000, 9000000000000],
      [9720000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-2160000000000, -9000000000000],
      [4320000000000, 18000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-4875000000000],
      [9720000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-4875000000000], [7560000000000,
      -9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.terminal (some (0, 3, 1)) (some (3, 3,
      1)) (some (3, 3, 1))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_5 : ExcludedOn (model16.B 5 ++ [step16.q]) 9000000000000 (model16.caps 5)
    (model16.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_6 : ExcludedOn (model16.B 6 ++ [step16.q]) 9000000000000 (model16.caps 6)
    (model16.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_7 : ExcludedOn (model16.B 7 ++ [step16.q]) 9000000000000 (model16.caps 7)
    (model16.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_8 : ExcludedOn (model16.B 8 ++ [step16.q]) 9000000000000 (model16.caps 8)
    (model16.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_9 : ExcludedOn (model16.B 9 ++ [step16.q]) 9000000000000 (model16.caps 9)
    (model16.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    (model17.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_1 : ExcludedOn (model17.B 1 ++ [step17.q]) 9000000000000 (model17.caps 1)
    (model17.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_2 : ExcludedOn (model17.B 2 ++ [step17.q]) 9000000000000 (model17.caps 2)
    (model17.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_3 : ExcludedOn (model17.B 3 ++ [step17.q]) 9000000000000 (model17.caps 3)
    (model17.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4320000000000], [1020000000000, -9000000000000])
      (some (1, 3, 1)) (some (2, 3, 1)) (.next ([6480000000000, 9000000000000], [3180000000000])
      (some (2, 3, 1)) (some (2, 3, 1)) (.next ([4320000000000], [3180000000000]) (some (2, 3, 1))
      (some (2, 3, 1)) (.next ([2160000000000, 9000000000000], [2160000000000, 9000000000000]) (some
      (2, 3, 1)) (some (3, 3, 1)) (.next ([0], [2160000000000, 9000000000000]) (some (3, 3, 1))
      (some (3, 3, 1)) (.next ([-1020000000000, 9000000000000], [5340000000000, -9000000000000])
      (some (3, 3, 1)) (some (3, 3, 1)) (.next ([-3180000000000, 0], [9660000000000, 9000000000000])
      (some (3, 0, 1)) (some (3, 0, 1)) (.next ([-3180000000000], [7500000000000]) (some (3, 0, 1))
      (some (3, 0, 1)) (.next ([-2160000000000, -9000000000000], [4320000000000, 18000000000000])
      (some (3, 0, 1)) (some (3, 0, 1)) (.terminal (some (3, 0, 1)) (some (3, 1, 1)) (some (3, 1,
      1))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded17_4 : ExcludedOn (model17.B 4 ++ [step17.q]) 9000000000000 (model17.caps 4)
    (model17.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_5 : ExcludedOn (model17.B 5 ++ [step17.q]) 9000000000000 (model17.caps 5)
    (model17.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_6 : ExcludedOn (model17.B 6 ++ [step17.q]) 9000000000000 (model17.caps 6)
    (model17.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_7 : ExcludedOn (model17.B 7 ++ [step17.q]) 9000000000000 (model17.caps 7)
    (model17.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_9 : ExcludedOn (model17.B 9 ++ [step17.q]) 9000000000000 (model17.caps 9)
    (model17.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded17_6
    · exact excluded17_7
    · exact (hj rfl).elim
    · exact excluded17_9
theorem next17 : model17.insert step17 = model18 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded18_0 : ExcludedOn (model18.B 0 ++ [step18.q]) 9000000000000 (model18.caps 0)
    (model18.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_1 : ExcludedOn (model18.B 1 ++ [step18.q]) 9000000000000 (model18.caps 1)
    (model18.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_2 : ExcludedOn (model18.B 2 ++ [step18.q]) 9000000000000 (model18.caps 2)
    (model18.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_3 : ExcludedOn (model18.B 3 ++ [step18.q]) 9000000000000 (model18.caps 3)
    (model18.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_4 : ExcludedOn (model18.B 4 ++ [step18.q]) 9000000000000 (model18.caps 4)
    (model18.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([345000000000], [15000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([2880000000000, 9000000000000], [1995000000000, -9000000000000])
      (some (5, 1, 2)) (some (5, 1, 3)) (.next ([4950000000000], [4155000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([2520000000000, 9000000000000], [2340000000000, -9000000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4590000000000], [4500000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([2070000000000, -9000000000000], [2160000000000, 9000000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2160000000000, 9000000000000], [4215000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([660000000000], [3495000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([720000000000], [4155000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([645000000000], [3855000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([360000000000], [4500000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([0],
      [4215000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-15000000000], [360000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-1995000000000, 9000000000000], [4875000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-4155000000000], [9105000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([-2340000000000, 9000000000000], [4860000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([-4500000000000], [9090000000000]) (some (5, 1, 3)) (some (5, 1, 4))
      (.next ([-2160000000000, -9000000000000], [4230000000000]) (some (5, 1, 4)) (some (5, 1, 4))
      (.next ([-4215000000000], [6375000000000, 9000000000000]) (some (5, 1, 4)) (some (5, 1, 5))
      (.next ([-3495000000000], [4155000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next
      ([-4155000000000], [4875000000000]) (some (5, 1, 5)) (some (5, 2, 5)) (.next
      ([-3855000000000], [4500000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next
      ([-4500000000000], [4860000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.terminal (some (5, 2,
      5)) (some (0, 2, 5)) (some (5, 2, 5))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_5 : ExcludedOn (model18.B 5 ++ [step18.q]) 9000000000000 (model18.caps 5)
    (model18.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_6 : ExcludedOn (model18.B 6 ++ [step18.q]) 9000000000000 (model18.caps 6)
    (model18.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_7 : ExcludedOn (model18.B 7 ++ [step18.q]) 9000000000000 (model18.caps 7)
    (model18.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_9 : ExcludedOn (model18.B 9 ++ [step18.q]) 9000000000000 (model18.caps 9)
    (model18.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked18 : StepValid model18 9000000000000 step18 0 1 100 := by
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
    · exact excluded18_4
    · exact excluded18_5
    · exact excluded18_6
    · exact excluded18_7
    · exact (hj rfl).elim
    · exact excluded18_9
theorem next18 : model18.insert step18 = model19 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded19_0 : ExcludedOn (model19.B 0 ++ [step19.q]) 9000000000000 (model19.caps 0)
    (model19.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_1 : ExcludedOn (model19.B 1 ++ [step19.q]) 9000000000000 (model19.caps 1)
    (model19.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_2 : ExcludedOn (model19.B 2 ++ [step19.q]) 9000000000000 (model19.caps 2)
    (model19.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_4 : ExcludedOn (model19.B 4 ++ [step19.q]) 9000000000000 (model19.caps 4)
    (model19.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([345000000000], [15000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) fan19Owner4Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_5 : ExcludedOn (model19.B 5 ++ [step19.q]) 9000000000000 (model19.caps 5)
    (model19.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_6 : ExcludedOn (model19.B 6 ++ [step19.q]) 9000000000000 (model19.caps 6)
    (model19.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_7 : ExcludedOn (model19.B 7 ++ [step19.q]) 9000000000000 (model19.caps 7)
    (model19.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_8 : ExcludedOn (model19.B 8 ++ [step19.q]) 9000000000000 (model19.caps 8)
    (model19.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4980000000000], [90000000000]) (some (0, 0, 4))
      (some (0, 1, 4)) (.next ([1500000000000], [90000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([3180000000000], [1500000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([4680000000000, 0], [2910000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([4680000000000], [5070000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([2160000000000,
      9000000000000], [2610000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([1500000000000], [3570000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([660000000000,
      9000000000000], [2520000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([0], [4770000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-90000000000],
      [5070000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-90000000000], [1590000000000])
      (some (0, 1, 4)) (some (0, 4, 4)) (.next ([-1500000000000], [4680000000000]) (some (0, 4, 4))
      (some (0, 4, 4)) (.next ([-2910000000000, 9000000000000], [7590000000000, -9000000000000])
      (some (0, 4, 4)) (some (0, 4, 4)) (.next ([-5070000000000], [9750000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-2610000000000, 9000000000000], [4770000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-3570000000000], [5070000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-2520000000000, 9000000000000], [3180000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.terminal (some (0, 4, 3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_9 : ExcludedOn (model19.B 9 ++ [step19.q]) 9000000000000 (model19.caps 9)
    (model19.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked19 : StepValid model19 9000000000000 step19 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded19_0
    · exact excluded19_1
    · exact excluded19_2
    · exact (hj rfl).elim
    · exact excluded19_4
    · exact excluded19_5
    · exact excluded19_6
    · exact excluded19_7
    · exact excluded19_8
    · exact excluded19_9
theorem next19 : model19.insert step19 = model20 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded20_0 : ExcludedOn (model20.B 0 ++ [step20.q]) 9000000000000 (model20.caps 0)
    (model20.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_2 : ExcludedOn (model20.B 2 ++ [step20.q]) 9000000000000 (model20.caps 2)
    (model20.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_4 : ExcludedOn (model20.B 4 ++ [step20.q]) 9000000000000 (model20.caps 4)
    (model20.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([345000000000], [15000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) fan20Owner4Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_5 : ExcludedOn (model20.B 5 ++ [step20.q]) 9000000000000 (model20.caps 5)
    (model20.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_6 : ExcludedOn (model20.B 6 ++ [step20.q]) 9000000000000 (model20.caps 6)
    (model20.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_7 : ExcludedOn (model20.B 7 ++ [step20.q]) 9000000000000 (model20.caps 7)
    (model20.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_8 : ExcludedOn (model20.B 8 ++ [step20.q]) 9000000000000 (model20.caps 8)
    (model20.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1500000000000], [90000000000]) (some (0, 0, 4))
      (some (0, 1, 4)) (.next ([3180000000000], [1500000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([4875000000000, 0], [2880000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([4875000000000], [5040000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([2160000000000, 9000000000000], [2610000000000, -9000000000000]) (some (0, 1, 4)) (some (0,
      1, 4)) (.next ([1695000000000], [3540000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([660000000000, 9000000000000], [2520000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1,
      4)) (.next ([105000000000], [5040000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [4770000000000]) (some (0, 1, 4)) (some (0, 4, 4)) (.next ([-90000000000], [1590000000000])
      (some (0, 4, 4)) (some (0, 4, 4)) (.next ([-1500000000000], [4680000000000]) (some (0, 4, 4))
      (some (0, 4, 4)) (.next ([-2880000000000, 9000000000000], [7755000000000, -9000000000000])
      (some (0, 4, 4)) (some (0, 4, 4)) (.next ([-5040000000000], [9915000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-2610000000000, 9000000000000], [4770000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-3540000000000], [5235000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-2520000000000, 9000000000000], [3180000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-5040000000000], [5145000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some
      (0, 4, 3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_9 : ExcludedOn (model20.B 9 ++ [step20.q]) 9000000000000 (model20.caps 9)
    (model20.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked20 : StepValid model20 9000000000000 step20 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded20_0
    · exact excluded20_1
    · exact excluded20_2
    · exact (hj rfl).elim
    · exact excluded20_4
    · exact excluded20_5
    · exact excluded20_6
    · exact excluded20_7
    · exact excluded20_8
    · exact excluded20_9
theorem next20 : model20.insert step20 = model21 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded21_0 : ExcludedOn (model21.B 0 ++ [step21.q]) 9000000000000 (model21.caps 0)
    (model21.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_1 : ExcludedOn (model21.B 1 ++ [step21.q]) 9000000000000 (model21.caps 1)
    (model21.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_2 : ExcludedOn (model21.B 2 ++ [step21.q]) 9000000000000 (model21.caps 2)
    (model21.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6840000000000, 9000000000000], [2628000000000,
      -9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2160000000000, 9000000000000],
      [2160000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4680000000000],
      [4788000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2520000000000, -9000000000000],
      [4788000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0, 0], [2160000000000,
      9000000000000]) (some (0, 3, 1)) (some (3, 3, 1)) (.next ([-2628000000000, 9000000000000],
      [9468000000000, 0]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([-2160000000000,
      -9000000000000], [4320000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-4788000000000], [9468000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-4788000000000,
      0], [7308000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded21_4 : ExcludedOn (model21.B 4 ++ [step21.q]) 9000000000000 (model21.caps 4)
    (model21.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([345000000000], [15000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([4377000000000], [555000000000]) (some (5, 1, 2)) (some (5, 1, 3))
      (.next ([4032000000000], [540000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      fan21Owner4Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded21_5 : ExcludedOn (model21.B 5 ++ [step21.q]) 9000000000000 (model21.caps 5)
    (model21.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_6 : ExcludedOn (model21.B 6 ++ [step21.q]) 9000000000000 (model21.caps 6)
    (model21.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_7 : ExcludedOn (model21.B 7 ++ [step21.q]) 9000000000000 (model21.caps 7)
    (model21.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_8 : ExcludedOn (model21.B 8 ++ [step21.q]) 9000000000000 (model21.caps 8)
    (model21.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_9 : ExcludedOn (model21.B 9 ++ [step21.q]) 9000000000000 (model21.caps 9)
    (model21.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked21 : StepValid model21 9000000000000 step21 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded21_0
    · exact excluded21_1
    · exact excluded21_2
    · exact (hj rfl).elim
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
    (model22.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6525000000000], [30000000000]) (some (7, 10, 4))
      (some (8, 10, 4)) (.next ([6525000000000], [345000000000]) (some (8, 10, 4)) (some (8, 10, 4))
      (.next ([7905000000000], [735000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([6360000000000], [765000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([8055000000000],
      [975000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([6045000000000], [1080000000000])
      (some (8, 10, 4)) (some (8, 10, 4)) (.next ([6120000000000], [1155000000000]) (some (8, 10,
      4)) (some (8, 10, 4)) (.next ([1530000000000], [315000000000]) (some (8, 10, 4)) (some (8, 10,
      4)) (.next ([5805000000000], [1470000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([5235000000000], [1485000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([4920000000000], [1485000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([4995000000000], [1875000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([4680000000000], [1875000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([1440000000000], [810000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([405000000000],
      [405000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([150000000000], [240000000000])
      (some (8, 10, 4)) (some (9, 10, 4)) (.next ([405000000000], [720000000000]) (some (9, 10, 4))
      (some (9, 10, 4)) fan22Owner0Part1)))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_1 : ExcludedOn (model22.B 1 ++ [step22.q]) 9000000000000 (model22.caps 1)
    (model22.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_2 : ExcludedOn (model22.B 2 ++ [step22.q]) 9000000000000 (model22.caps 2)
    (model22.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_3 : ExcludedOn (model22.B 3 ++ [step22.q]) 9000000000000 (model22.caps 3)
    (model22.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_4 : ExcludedOn (model22.B 4 ++ [step22.q]) 9000000000000 (model22.caps 4)
    (model22.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([345000000000], [15000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) fan22Owner4Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_6 : ExcludedOn (model22.B 6 ++ [step22.q]) 9000000000000 (model22.caps 6)
    (model22.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_7 : ExcludedOn (model22.B 7 ++ [step22.q]) 9000000000000 (model22.caps 7)
    (model22.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_8 : ExcludedOn (model22.B 8 ++ [step22.q]) 9000000000000 (model22.caps 8)
    (model22.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_9 : ExcludedOn (model22.B 9 ++ [step22.q]) 9000000000000 (model22.caps 9)
    (model22.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked22 : StepValid model22 9000000000000 step22 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded22_0
    · exact excluded22_1
    · exact excluded22_2
    · exact excluded22_3
    · exact excluded22_4
    · exact (hj rfl).elim
    · exact excluded22_6
    · exact excluded22_7
    · exact excluded22_8
    · exact excluded22_9
theorem next22 : model22.insert step22 = model23 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded23_0 : ExcludedOn (model23.B 0 ++ [step23.q]) 9000000000000 (model23.caps 0)
    (model23.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_1 : ExcludedOn (model23.B 1 ++ [step23.q]) 9000000000000 (model23.caps 1)
    (model23.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_2 : ExcludedOn (model23.B 2 ++ [step23.q]) 9000000000000 (model23.caps 2)
    (model23.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_3 : ExcludedOn (model23.B 3 ++ [step23.q]) 9000000000000 (model23.caps 3)
    (model23.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3405000000000], [87000000000]) (some (4, 6, 3))
      (some (6, 6, 3)) (.next ([4875000000000], [855000000000]) (some (6, 6, 3)) (some (6, 6, 3))
      (.next ([4680000000000], [885000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next
      ([3930000000000], [750000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next ([3960000000000],
      [915000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next ([1770000000000, -9000000000000],
      [750000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next ([1800000000000, -9000000000000],
      [915000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next ([2628000000000, -9000000000000],
      [1692000000000, 9000000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next ([2628000000000,
      9000000000000], [2160000000000, -9000000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next
      ([4788000000000], [4347000000000]) (some (6, 2, 3)) (some (6, 2, 4)) (.next ([2160000000000,
      9000000000000], [2160000000000, 9000000000000]) (some (6, 2, 4)) (some (6, 2, 4))
      fan23Owner3Part0)))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded23_4 : ExcludedOn (model23.B 4 ++ [step23.q]) 9000000000000 (model23.caps 4)
    (model23.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_5 : ExcludedOn (model23.B 5 ++ [step23.q]) 9000000000000 (model23.caps 5)
    (model23.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_6 : ExcludedOn (model23.B 6 ++ [step23.q]) 9000000000000 (model23.caps 6)
    (model23.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_7 : ExcludedOn (model23.B 7 ++ [step23.q]) 9000000000000 (model23.caps 7)
    (model23.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_9 : ExcludedOn (model23.B 9 ++ [step23.q]) 9000000000000 (model23.caps 9)
    (model23.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked23 : StepValid model23 9000000000000 step23 0 1 100 := by
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

end Sext240000250000
end ConwaySoifer.Simplified.Certificates
