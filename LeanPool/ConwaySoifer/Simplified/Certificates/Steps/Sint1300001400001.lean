/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint130000140000
import Mathlib.Tactic.FinCases

/-!
# Sint 130000 140000 1

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
namespace Sint130000140000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan8Owner0Part0 : FanWitness := (.next ([280800000000, 5160000000000], [4929600000000,
    -2580000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([24600000000, -2580000000000],
    [1045800000000, 5160000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-54600000000,
    2580000000000], [5600400000000, 2580000000000]) (some (7, 3, 5)) (some (7, 3, 6)) (.next
    ([-454200000000, 5160000000000], [5154600000000, -2580000000000]) (some (7, 3, 6)) (some (7, 3,
    6)) (.next ([-695400000000, -2580000000000], [5905800000000, 5160000000000]) (some (7, 3, 6))
    (some (7, 3, 6)) (.next ([-725400000000, -2580000000000], [5935800000000, 5160000000000]) (some
    (7, 3, 6)) (some (7, 3, 6)) (.next ([-789600000000, 2580000000000], [5825400000000,
    2580000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-1095000000000], [5595000000000])
    (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-1125000000000], [5625000000000]) (some (7, 3, 6))
    (some (7, 3, 6)) (.next ([-1460400000000, -2580000000000], [6160800000000, 5160000000000]) (some
    (7, 3, 6)) (some (7, 3, 6)) (.next ([-1860000000000], [5850000000000]) (some (7, 3, 6)) (some
    (7, 3, 6)) (.next ([-4455000000000], [10050000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next
    ([-4485000000000], [10050000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-4710000000000],
    [9540000000000]) (some (7, 3, 6)) (some (7, 4, 6)) (.next ([-335400000000, -2580000000000],
    [670800000000, 5160000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-710400000000,
    -2580000000000], [1405800000000, 5160000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-510000000000], [765000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-510000000000],
    [735000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-4839600000000, 2580000000000],
    [6290400000000, 2580000000000]) (some (7, 4, 0)) (some (7, 4, 0)) (.next ([-4504200000000,
    5160000000000], [5619600000000, -2580000000000]) (some (7, 4, 0)) (some (7, 4, 0)) (.next
    ([-5550000000000], [6690000000000]) (some (7, 4, 0)) (some (7, 4, 0)) (.next ([-4839600000000,
    2580000000000], [5284200000000, -5160000000000]) (some (7, 4, 0)) (some (7, 4, 0)) (.next
    ([-4899600000000, 2580000000000], [5210400000000, 2580000000000]) (some (7, 4, 0)) (some (7, 4,
    0)) (.next ([-4929600000000, 2580000000000], [5210400000000, 2580000000000]) (some (7, 4, 0))
    (some (7, 4, 0)) (.terminal (some (7, 4, 0)) (some (7, 4, 0)) (some (7, 4,
    0)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan10Owner0Part0 : FanWitness := (.next ([280800000000, 5160000000000], [4929600000000,
    -2580000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([24600000000, -2580000000000],
    [1045800000000, 5160000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-54600000000,
    2580000000000], [5600400000000, 2580000000000]) (some (7, 3, 5)) (some (7, 3, 6)) (.next
    ([-170700000000, 5160000000000], [8079600000000, -2580000000000]) (some (7, 3, 6)) (some (7, 3,
    6)) (.next ([-506100000000, 2580000000000], [8750400000000, 2580000000000]) (some (7, 3, 6))
    (some (7, 3, 6)) (.next ([-506100000000, 2580000000000], [7744200000000, -5160000000000]) (some
    (7, 3, 6)) (some (7, 3, 6)) (.next ([-454200000000, 5160000000000], [5154600000000,
    -2580000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-695400000000, -2580000000000],
    [5905800000000, 5160000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-725400000000,
    -2580000000000], [5935800000000, 5160000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next
    ([-1216500000000], [9150000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-1095000000000],
    [5595000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-1125000000000], [5625000000000])
    (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-1460400000000, -2580000000000], [6160800000000,
    5160000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-1860000000000], [5850000000000])
    (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-310800000000, -5160000000000], [710400000000,
    2580000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-335400000000, -2580000000000],
    [670800000000, 5160000000000]) (some (7, 3, 6)) (some (7, 4, 6)) (.next ([-710400000000,
    -2580000000000], [1405800000000, 5160000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-510000000000], [765000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-510000000000],
    [735000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5716500000000], [8055000000000])
    (some (7, 4, 0)) (some (7, 4, 0)) (.next ([-5716500000000], [8025000000000]) (some (7, 4, 0))
    (some (7, 4, 0)) (.next ([-5206500000000], [7290000000000]) (some (7, 4, 0)) (some (7, 4, 0))
    (.next ([-4899600000000, 2580000000000], [5210400000000, 2580000000000]) (some (7, 4, 0)) (some
    (7, 4, 7)) (.next ([-4929600000000, 2580000000000], [5210400000000, 2580000000000]) (some (7, 4,
    7)) (some (7, 4, 7)) (.terminal (some (7, 4, 7)) (some (7, 4, 7)) (some (7, 4,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan10Owner4Part0 : FanWitness := (.next ([8158500000000, 0], [585000000000, 9000000000000])
    (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3988500000000], [585000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([3045000000000], [780000000000]) (some (5, 1, 2)) (some (5, 1, 2))
    (.next ([4333500000000], [2460000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([1170000000000, 9000000000000], [1170000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1,
    5)) (.next ([1875000000000, -9000000000000], [1950000000000, 9000000000000]) (some (5, 1, 5))
    (some (5, 1, 5)) (.next ([1170000000000], [1830000000000, -9000000000000]) (some (5, 1, 5))
    (some (5, 1, 5)) (.next ([1170000000000], [3000000000000]) (some (5, 1, 5)) (some (5, 1, 5))
    (.next ([345000000000], [1875000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next
    ([585000000000], [6403500000000, -9000000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next
    ([585000000000], [7573500000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0, 0],
    [1170000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0, -9000000000000],
    [4170000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-585000000000,
    -9000000000000], [8743500000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-585000000000], [4573500000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-780000000000],
    [3825000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2460000000000], [6793500000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1170000000000, -9000000000000], [2340000000000,
    18000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1950000000000, -9000000000000],
    [3825000000000, 0]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1830000000000, 9000000000000],
    [3000000000000, -9000000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-3000000000000],
    [4170000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1875000000000], [2220000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-6403500000000, 9000000000000], [6988500000000,
    -9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-7573500000000], [8158500000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan12Owner4Part0 : FanWitness := (.next ([7545000000000, 9000000000000], [810000000000,
    -9000000000000]) (some (3, 1, 5)) (some (3, 1, 5)) (.next ([3045000000000], [780000000000])
    (some (3, 1, 5)) (some (3, 1, 5)) (.next ([6375000000000], [1980000000000]) (some (3, 1, 5))
    (some (3, 1, 5)) (.next ([5205000000000, -9000000000000], [1980000000000, 0]) (some (3, 1, 5))
    (some (3, 1, 5)) (.next ([1170000000000, 9000000000000], [1170000000000, 9000000000000]) (some
    (3, 1, 5)) (some (3, 5, 5)) (.next ([1875000000000, -9000000000000], [1950000000000,
    9000000000000]) (some (3, 5, 5)) (some (3, 5, 5)) (.next ([1170000000000], [1830000000000,
    -9000000000000]) (some (3, 5, 5)) (some (3, 5, 5)) (.next ([1170000000000], [3000000000000])
    (some (3, 5, 5)) (some (4, 5, 5)) (.next ([1845000000000], [5310000000000]) (some (4, 5, 5))
    (some (4, 5, 5)) (.next ([2190000000000], [7185000000000]) (some (4, 5, 2)) (some (4, 5, 2))
    (.next ([345000000000], [1875000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([0, 0],
    [1170000000000, 9000000000000]) (some (4, 5, 2)) (some (4, 5, 3)) (.next ([0, -9000000000000],
    [4170000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-810000000000,
    9000000000000], [8355000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-780000000000],
    [3825000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1980000000000], [8355000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1980000000000, 0], [7185000000000, -9000000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1170000000000, -9000000000000], [2340000000000,
    18000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1950000000000, -9000000000000],
    [3825000000000, 0]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1830000000000, 9000000000000],
    [3000000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3000000000000],
    [4170000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-5310000000000], [7155000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-7185000000000], [9375000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-1875000000000], [2220000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan13Owner4Part0 : FanWitness := (.next ([7545000000000, 9000000000000], [936000000000,
    -9000000000000]) (some (3, 1, 5)) (some (3, 1, 5)) (.next ([3045000000000], [780000000000])
    (some (3, 1, 5)) (some (3, 1, 5)) (.next ([6375000000000], [2106000000000]) (some (3, 1, 5))
    (some (3, 1, 5)) (.next ([5205000000000, -9000000000000], [2106000000000, 0]) (some (3, 1, 5))
    (some (3, 1, 5)) (.next ([1170000000000, 9000000000000], [1170000000000, 9000000000000]) (some
    (3, 1, 5)) (some (3, 5, 5)) (.next ([1875000000000, -9000000000000], [1950000000000,
    9000000000000]) (some (3, 5, 5)) (some (3, 5, 5)) (.next ([1170000000000], [1830000000000,
    -9000000000000]) (some (3, 5, 5)) (some (3, 5, 5)) (.next ([1170000000000], [3000000000000])
    (some (3, 5, 5)) (some (4, 5, 5)) (.next ([1719000000000], [5436000000000]) (some (4, 5, 5))
    (some (4, 5, 5)) (.next ([2064000000000], [7311000000000]) (some (4, 5, 2)) (some (4, 5, 2))
    (.next ([345000000000], [1875000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([0, 0],
    [1170000000000, 9000000000000]) (some (4, 5, 2)) (some (4, 5, 3)) (.next ([0, -9000000000000],
    [4170000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-936000000000,
    9000000000000], [8481000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-780000000000],
    [3825000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2106000000000], [8481000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2106000000000, 0], [7311000000000, -9000000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1170000000000, -9000000000000], [2340000000000,
    18000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1950000000000, -9000000000000],
    [3825000000000, 0]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1830000000000, 9000000000000],
    [3000000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3000000000000],
    [4170000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-5436000000000], [7155000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-7311000000000], [9375000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-1875000000000], [2220000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner0Part0 : FanWitness := (.next ([0, 0], [1006200000000, 7740000000000]) (some (7, 3,
    5)) (some (7, 3, 5)) (.next ([-54600000000, 2580000000000], [5600400000000, 2580000000000])
    (some (7, 3, 5)) (some (7, 3, 6)) (.next ([-454200000000, 5160000000000], [5154600000000,
    -2580000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-695400000000, -2580000000000],
    [5905800000000, 5160000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-725400000000,
    -2580000000000], [5935800000000, 5160000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next
    ([-789600000000, 2580000000000], [5825400000000, 2580000000000]) (some (7, 3, 6)) (some (7, 3,
    6)) (.next ([-1095000000000], [5595000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next
    ([-1125000000000], [5625000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-1460400000000,
    -2580000000000], [6160800000000, 5160000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next
    ([-2689200000000, 5160000000000], [8664600000000, -2580000000000]) (some (7, 3, 6)) (some (7, 3,
    6)) (.next ([-1860000000000], [5850000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next
    ([-3024600000000, 2580000000000], [9335400000000, 2580000000000]) (some (7, 3, 6)) (some (7, 3,
    6)) (.next ([-3024600000000, 2580000000000], [8329200000000, -5160000000000]) (some (7, 3, 6))
    (some (7, 3, 6)) (.next ([-3735000000000], [9735000000000]) (some (7, 3, 6)) (some (7, 3, 6))
    (.next ([-310800000000, -5160000000000], [710400000000, 2580000000000]) (some (7, 3, 6)) (some
    (7, 3, 6)) (.next ([-335400000000, -2580000000000], [670800000000, 5160000000000]) (some (7, 3,
    6)) (some (7, 4, 6)) (.next ([-710400000000, -2580000000000], [1405800000000, 5160000000000])
    (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-510000000000], [765000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-510000000000], [735000000000]) (some (7, 4, 6)) (some (7, 4, 6))
    (.next ([-4899600000000, 2580000000000], [5210400000000, 2580000000000]) (some (7, 4, 0)) (some
    (7, 4, 0)) (.next ([-4929600000000, 2580000000000], [5210400000000, 2580000000000]) (some (7, 4,
    0)) (some (7, 4, 0)) (.next ([-8235000000000], [8640000000000]) (some (7, 4, 0)) (some (7, 4,
    0)) (.next ([-8235000000000], [8610000000000]) (some (7, 4, 0)) (some (7, 4, 0)) (.next
    ([-7725000000000], [7875000000000]) (some (7, 4, 0)) (some (7, 4, 0)) (.terminal (some (7, 4,
    0)) (some (7, 4, 7)) (some (7, 4, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner0Part0 : FanWitness := (.next ([249600000000, -2580000000000], [4914600000000,
    -2580000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([24600000000, -2580000000000],
    [1045800000000, 5160000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-54600000000,
    2580000000000], [5600400000000, 2580000000000]) (some (7, 3, 5)) (some (7, 3, 6)) (.next
    ([-454200000000, 5160000000000], [5154600000000, -2580000000000]) (some (7, 3, 6)) (some (7, 3,
    6)) (.next ([-695400000000, -2580000000000], [5905800000000, 5160000000000]) (some (7, 3, 6))
    (some (7, 3, 6)) (.next ([-725400000000, -2580000000000], [5935800000000, 5160000000000]) (some
    (7, 3, 6)) (some (7, 3, 6)) (.next ([-789600000000, 2580000000000], [5825400000000,
    2580000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-1095000000000], [5595000000000])
    (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-1125000000000], [5625000000000]) (some (7, 3, 6))
    (some (7, 3, 6)) (.next ([-1460400000000, -2580000000000], [6160800000000, 5160000000000]) (some
    (7, 3, 6)) (some (7, 3, 6)) (.next ([-1860000000000], [5850000000000]) (some (7, 3, 6)) (some
    (7, 3, 6)) (.next ([-4650000000000], [10125000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next
    ([-4680000000000], [10125000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-335400000000,
    -2580000000000], [670800000000, 5160000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next
    ([-710400000000, -2580000000000], [1405800000000, 5160000000000]) (some (7, 4, 6)) (some (7, 4,
    6)) (.next ([-4905000000000], [9615000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-510000000000], [765000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-510000000000],
    [735000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-4914600000000, 2580000000000],
    [6170400000000, 2580000000000]) (some (7, 4, 0)) (some (7, 4, 0)) (.next ([-4579200000000,
    5160000000000], [5499600000000, -2580000000000]) (some (7, 4, 0)) (some (7, 4, 0)) (.next
    ([-5625000000000], [6570000000000]) (some (7, 4, 0)) (some (7, 4, 0)) (.next ([-4899600000000,
    2580000000000], [5210400000000, 2580000000000]) (some (7, 4, 0)) (some (7, 4, 0)) (.next
    ([-4929600000000, 2580000000000], [5210400000000, 2580000000000]) (some (7, 4, 0)) (some (7, 4,
    0)) (.next ([-4914600000000, 2580000000000], [5164200000000, -5160000000000]) (some (7, 4, 0))
    (some (7, 4, 0)) (.terminal (some (7, 4, 0)) (some (7, 4, 0)) (some (7, 4,
    0)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner5Part0 : FanWitness := (.next ([1596000000000], [510000000000]) (some (5, 1, 2)) (some
    (5, 1, 2)) (.next ([1980000000000], [645000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([1470000000000], [510000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2115000000000, 0],
    [1170000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3750000000000],
    [3720000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3750000000000], [5835000000000])
    (some (5, 1, 2)) (some (5, 1, 2)) (.next ([936000000000, -9000000000000], [1689000000000,
    9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([810000000000, -9000000000000],
    [1815000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next ([2580000000000,
    -9000000000000], [7005000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([1770000000000], [5190000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1644000000000],
    [5316000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([0], [2115000000000]) (some (5, 1,
    3)) (some (5, 1, 5)) (.next ([-519000000000], [2625000000000]) (some (5, 1, 5)) (some (5, 2, 5))
    (.next ([-510000000000], [2106000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next
    ([-645000000000], [2625000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-510000000000],
    [1980000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-1170000000000, -9000000000000],
    [3285000000000, 9000000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-3720000000000],
    [7470000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-5835000000000], [9585000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1689000000000, -9000000000000], [2625000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1815000000000, -9000000000000], [2625000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-7005000000000, -9000000000000], [9585000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5190000000000], [6960000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-5316000000000], [6960000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

theorem excluded8_0 : ExcludedOn (model8.B 0 ++ [step8.q]) 9000000000000 (model8.caps 0) (model8.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5545800000000, 5160000000000], [54600000000,
      -2580000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([4700400000000, 2580000000000],
      [454200000000, -5160000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([5210400000000,
      2580000000000], [695400000000, 2580000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
      ([5210400000000, 2580000000000], [725400000000, 2580000000000]) (some (0, 7, 4)) (some (0, 7,
      4)) (.next ([5035800000000, 5160000000000], [789600000000, -2580000000000]) (some (0, 7, 4))
      (some (0, 7, 4)) (.next ([4500000000000], [1095000000000]) (some (0, 7, 4)) (some (0, 7, 4))
      (.next ([4500000000000], [1125000000000]) (some (0, 7, 4)) (some (0, 7, 5)) (.next
      ([4700400000000, 2580000000000], [1460400000000, 2580000000000]) (some (0, 7, 5)) (some (0, 7,
      5)) (.next ([3990000000000], [1860000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
      ([5595000000000], [4455000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([5565000000000],
      [4485000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([4830000000000], [4710000000000])
      (some (0, 7, 5)) (some (0, 7, 5)) (.next ([335400000000, 2580000000000], [335400000000,
      2580000000000]) (some (0, 7, 5)) (some (7, 7, 5)) (.next ([695400000000, 2580000000000],
      [710400000000, 2580000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([255000000000],
      [510000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([225000000000], [510000000000])
      (some (7, 7, 5)) (some (7, 7, 5)) (.next ([1450800000000, 5160000000000], [4839600000000,
      -2580000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([1115400000000, 2580000000000],
      [4504200000000, -5160000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([1140000000000],
      [5550000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([444600000000, -2580000000000],
      [4839600000000, -2580000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([310800000000,
      5160000000000], [4899600000000, -2580000000000]) (some (7, 3, 5)) (some (7, 3, 5))
      fan8Owner0Part0)))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_1 : ExcludedOn (model8.B 1 ++ [step8.q]) 9000000000000 (model8.caps 1) (model8.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_2 : ExcludedOn (model8.B 2 ++ [step8.q]) 9000000000000 (model8.caps 2) (model8.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_3 : ExcludedOn (model8.B 3 ++ [step8.q]) 9000000000000 (model8.caps 3) (model8.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_5 : ExcludedOn (model8.B 5 ++ [step8.q]) 9000000000000 (model8.caps 5) (model8.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1170000000000, 9000000000000], [1170000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([3825000000000, 0], [4785000000000,
      -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([3825000000000], [5955000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2655000000000, -9000000000000], [7125000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [1170000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-1170000000000, -9000000000000],
      [2340000000000, 18000000000000]) (some (3, 1, 3)) (some (3, 2, 3)) (.next ([-4785000000000,
      9000000000000], [8610000000000, -9000000000000]) (some (3, 2, 3)) (some (3, 2, 3)) (.next
      ([-5955000000000], [9780000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-7125000000000,
      -9000000000000], [9780000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_6 : ExcludedOn (model8.B 6 ++ [step8.q]) 9000000000000 (model8.caps 6) (model8.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_7 : ExcludedOn (model8.B 7 ++ [step8.q]) 9000000000000 (model8.caps 7) (model8.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_8 : ExcludedOn (model8.B 8 ++ [step8.q]) 9000000000000 (model8.caps 8) (model8.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_9 : ExcludedOn (model8.B 9 ++ [step8.q]) 9000000000000 (model8.caps 9) (model8.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked8 : StepValid model8 9000000000000 step8 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded8_0
    · exact excluded8_1
    · exact excluded8_2
    · exact excluded8_3
    · exact (hj rfl).elim
    · exact excluded8_5
    · exact excluded8_6
    · exact excluded8_7
    · exact excluded8_8
    · exact excluded8_9
theorem next8 : model8.insert step8 = model9 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded9_0 : ExcludedOn (model9.B 0 ++ [step9.q]) 9000000000000 (model9.caps 0) (model9.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_1 : ExcludedOn (model9.B 1 ++ [step9.q]) 9000000000000 (model9.caps 1) (model9.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_2 : ExcludedOn (model9.B 2 ++ [step9.q]) 9000000000000 (model9.caps 2) (model9.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_3 : ExcludedOn (model9.B 3 ++ [step9.q]) 9000000000000 (model9.caps 3) (model9.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_4 : ExcludedOn (model9.B 4 ++ [step9.q]) 9000000000000 (model9.caps 4) (model9.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4170000000000, 0], [0, 9000000000000]) (some (5,
      0, 2)) (some (5, 1, 2)) (.next ([5475000000000, -9000000000000], [1170000000000,
      9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3045000000000], [780000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([5865000000000], [3825000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([1170000000000, 9000000000000], [1170000000000, 9000000000000]) (some
      (5, 1, 2)) (some (5, 1, 2)) (.next ([1875000000000, -9000000000000], [1950000000000,
      9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3645000000000], [4170000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1170000000000], [1830000000000, -9000000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1170000000000], [3000000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([345000000000], [1875000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([0, 0], [1170000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next ([0,
      -9000000000000], [4170000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([-1170000000000, -9000000000000], [6645000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([-780000000000], [3825000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-3825000000000],
      [9690000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-1170000000000, -9000000000000],
      [2340000000000, 18000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-1950000000000,
      -9000000000000], [3825000000000, 0]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([-4170000000000], [7815000000000]) (some (5, 1, 3)) (some (5, 2, 3)) (.next ([-1830000000000,
      9000000000000], [3000000000000, -9000000000000]) (some (5, 2, 3)) (some (5, 2, 5)) (.next
      ([-3000000000000], [4170000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next
      ([-1875000000000], [2220000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.terminal (some (5, 2,
      5)) (some (0, 2, 5)) (some (5, 2, 5))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_5 : ExcludedOn (model9.B 5 ++ [step9.q]) 9000000000000 (model9.caps 5) (model9.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_6 : ExcludedOn (model9.B 6 ++ [step9.q]) 9000000000000 (model9.caps 6) (model9.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_7 : ExcludedOn (model9.B 7 ++ [step9.q]) 9000000000000 (model9.caps 7) (model9.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_9 : ExcludedOn (model9.B 9 ++ [step9.q]) 9000000000000 (model9.caps 9) (model9.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked9 : StepValid model9 9000000000000 step9 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded9_0
    · exact excluded9_1
    · exact excluded9_2
    · exact excluded9_3
    · exact excluded9_4
    · exact excluded9_5
    · exact excluded9_6
    · exact excluded9_7
    · exact (hj rfl).elim
    · exact excluded9_9
theorem next9 : model9.insert step9 = model10 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded10_0 : ExcludedOn (model10.B 0 ++ [step10.q]) 9000000000000 (model10.caps 0)
    (model10.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5545800000000, 5160000000000], [54600000000,
      -2580000000000]) (some (7, 7, 4)) (some (7, 7, 4)) (.next ([7908900000000, 2580000000000],
      [170700000000, -5160000000000]) (some (7, 7, 4)) (some (7, 7, 4)) (.next ([8244300000000,
      5160000000000], [506100000000, -2580000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next
      ([7238100000000, -2580000000000], [506100000000, -2580000000000]) (some (7, 2, 4)) (some (7,
      2, 4)) (.next ([4700400000000, 2580000000000], [454200000000, -5160000000000]) (some (7, 2,
      4)) (some (7, 2, 4)) (.next ([5210400000000, 2580000000000], [695400000000, 2580000000000])
      (some (7, 2, 4)) (some (7, 2, 4)) (.next ([5210400000000, 2580000000000], [725400000000,
      2580000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([7933500000000], [1216500000000])
      (some (7, 2, 4)) (some (7, 2, 4)) (.next ([4500000000000], [1095000000000]) (some (7, 2, 4))
      (some (7, 2, 4)) (.next ([4500000000000], [1125000000000]) (some (7, 2, 4)) (some (7, 2, 5))
      (.next ([4700400000000, 2580000000000], [1460400000000, 2580000000000]) (some (7, 2, 5)) (some
      (7, 2, 5)) (.next ([3990000000000], [1860000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
      ([399600000000, -2580000000000], [310800000000, 5160000000000]) (some (7, 2, 5)) (some (7, 2,
      5)) (.next ([335400000000, 2580000000000], [335400000000, 2580000000000]) (some (7, 2, 5))
      (some (7, 2, 5)) (.next ([695400000000, 2580000000000], [710400000000, 2580000000000]) (some
      (7, 2, 5)) (some (7, 3, 5)) (.next ([255000000000], [510000000000]) (some (7, 3, 5)) (some (7,
      3, 5)) (.next ([225000000000], [510000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
      ([2338500000000], [5716500000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([2308500000000],
      [5716500000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([2083500000000], [5206500000000])
      (some (7, 3, 5)) (some (7, 3, 5)) (.next ([310800000000, 5160000000000], [4899600000000,
      -2580000000000]) (some (7, 3, 5)) (some (7, 3, 5)) fan10Owner0Part0)))))))))))))))))))))) (den
      := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded10_1 : ExcludedOn (model10.B 1 ++ [step10.q]) 9000000000000 (model10.caps 1)
    (model10.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_2 : ExcludedOn (model10.B 2 ++ [step10.q]) 9000000000000 (model10.caps 2)
    (model10.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_4 : ExcludedOn (model10.B 4 ++ [step10.q]) 9000000000000 (model10.caps 4)
    (model10.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4170000000000, 0], [0, 9000000000000]) (some (5,
      0, 2)) (some (5, 1, 2)) fan10Owner4Part0)) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded10_5 : ExcludedOn (model10.B 5 ++ [step10.q]) 9000000000000 (model10.caps 5)
    (model10.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_6 : ExcludedOn (model10.B 6 ++ [step10.q]) 9000000000000 (model10.caps 6)
    (model10.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_7 : ExcludedOn (model10.B 7 ++ [step10.q]) 9000000000000 (model10.caps 7)
    (model10.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_8 : ExcludedOn (model10.B 8 ++ [step10.q]) 9000000000000 (model10.caps 8)
    (model10.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7230000000000], [928500000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([4470000000000], [2355000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([1426500000000], [1333500000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1426500000000], [8158500000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [2355000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-928500000000], [8158500000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2355000000000], [6825000000000]) (some (0, 1, 3))
      (some (0, 3, 3)) (.next ([-1333500000000], [2760000000000]) (some (0, 3, 3)) (some (0, 3, 3))
      (.next ([-8158500000000], [9585000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded10_9 : ExcludedOn (model10.B 9 ++ [step10.q]) 9000000000000 (model10.caps 9)
    (model10.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked10 : StepValid model10 9000000000000 step10 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded10_0
    · exact excluded10_1
    · exact excluded10_2
    · exact (hj rfl).elim
    · exact excluded10_4
    · exact excluded10_5
    · exact excluded10_6
    · exact excluded10_7
    · exact excluded10_8
    · exact excluded10_9
theorem next10 : model10.insert step10 = model11 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded11_0 : ExcludedOn (model11.B 0 ++ [step11.q]) 9000000000000 (model11.caps 0)
    (model11.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_1 : ExcludedOn (model11.B 1 ++ [step11.q]) 9000000000000 (model11.caps 1)
    (model11.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_2 : ExcludedOn (model11.B 2 ++ [step11.q]) 9000000000000 (model11.caps 2)
    (model11.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_3 : ExcludedOn (model11.B 3 ++ [step11.q]) 9000000000000 (model11.caps 3)
    (model11.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_4 : ExcludedOn (model11.B 4 ++ [step11.q]) 9000000000000 (model11.caps 4)
    (model11.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4170000000000, 0], [0, 9000000000000]) (some (3,
      0, 5)) (some (3, 5, 5)) (.next ([3045000000000], [780000000000]) (some (3, 5, 5)) (some (3, 5,
      5)) (.next ([1170000000000, 9000000000000], [1170000000000, 9000000000000]) (some (3, 5, 5))
      (some (3, 5, 5)) (.next ([3825000000000], [3840000000000]) (some (3, 5, 5)) (some (3, 5, 5))
      (.next ([1875000000000, -9000000000000], [1950000000000, 9000000000000]) (some (3, 5, 2))
      (some (3, 5, 2)) (.next ([4170000000000], [5715000000000]) (some (3, 5, 2)) (some (3, 5, 2))
      (.next ([1170000000000], [1830000000000, -9000000000000]) (some (3, 5, 2)) (some (3, 5, 2))
      (.next ([1170000000000], [3000000000000]) (some (3, 5, 2)) (some (4, 5, 2)) (.next
      ([345000000000], [1875000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([1170000000000,
      9000000000000], [6885000000000]) (some (4, 5, 2)) (some (4, 5, 3)) (.next ([0, 0],
      [1170000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0, -9000000000000],
      [4170000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-780000000000],
      [3825000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1170000000000, -9000000000000],
      [2340000000000, 18000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3840000000000],
      [7665000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1950000000000, -9000000000000],
      [3825000000000, 0]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-5715000000000],
      [9885000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1830000000000, 9000000000000],
      [3000000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3000000000000],
      [4170000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1875000000000], [2220000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-6885000000000], [8055000000000, 9000000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5,
      3))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded11_6 : ExcludedOn (model11.B 6 ++ [step11.q]) 9000000000000 (model11.caps 6)
    (model11.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_7 : ExcludedOn (model11.B 7 ++ [step11.q]) 9000000000000 (model11.caps 7)
    (model11.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_8 : ExcludedOn (model11.B 8 ++ [step11.q]) 9000000000000 (model11.caps 8)
    (model11.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_9 : ExcludedOn (model11.B 9 ++ [step11.q]) 9000000000000 (model11.caps 9)
    (model11.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked11 : StepValid model11 9000000000000 step11 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded11_0
    · exact excluded11_1
    · exact excluded11_2
    · exact excluded11_3
    · exact excluded11_4
    · exact (hj rfl).elim
    · exact excluded11_6
    · exact excluded11_7
    · exact excluded11_8
    · exact excluded11_9
theorem next11 : model11.insert step11 = model12 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded12_0 : ExcludedOn (model12.B 0 ++ [step12.q]) 9000000000000 (model12.caps 0)
    (model12.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_1 : ExcludedOn (model12.B 1 ++ [step12.q]) 9000000000000 (model12.caps 1)
    (model12.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_2 : ExcludedOn (model12.B 2 ++ [step12.q]) 9000000000000 (model12.caps 2)
    (model12.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_3 : ExcludedOn (model12.B 3 ++ [step12.q]) 9000000000000 (model12.caps 3)
    (model12.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_4 : ExcludedOn (model12.B 4 ++ [step12.q]) 9000000000000 (model12.caps 4)
    (model12.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4170000000000, 0], [0, 9000000000000]) (some (3,
      0, 5)) (some (3, 1, 5)) fan12Owner4Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded12_6 : ExcludedOn (model12.B 6 ++ [step12.q]) 9000000000000 (model12.caps 6)
    (model12.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_7 : ExcludedOn (model12.B 7 ++ [step12.q]) 9000000000000 (model12.caps 7)
    (model12.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_8 : ExcludedOn (model12.B 8 ++ [step12.q]) 9000000000000 (model12.caps 8)
    (model12.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_9 : ExcludedOn (model12.B 9 ++ [step12.q]) 9000000000000 (model12.caps 9)
    (model12.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked12 : StepValid model12 9000000000000 step12 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded12_0
    · exact excluded12_1
    · exact excluded12_2
    · exact excluded12_3
    · exact excluded12_4
    · exact (hj rfl).elim
    · exact excluded12_6
    · exact excluded12_7
    · exact excluded12_8
    · exact excluded12_9
theorem next12 : model12.insert step12 = model13 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded13_0 : ExcludedOn (model13.B 0 ++ [step13.q]) 9000000000000 (model13.caps 0)
    (model13.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_1 : ExcludedOn (model13.B 1 ++ [step13.q]) 9000000000000 (model13.caps 1)
    (model13.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_2 : ExcludedOn (model13.B 2 ++ [step13.q]) 9000000000000 (model13.caps 2)
    (model13.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_3 : ExcludedOn (model13.B 3 ++ [step13.q]) 9000000000000 (model13.caps 3)
    (model13.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_4 : ExcludedOn (model13.B 4 ++ [step13.q]) 9000000000000 (model13.caps 4)
    (model13.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4170000000000, 0], [0, 9000000000000]) (some (3,
      0, 5)) (some (3, 1, 5)) fan13Owner4Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_6 : ExcludedOn (model13.B 6 ++ [step13.q]) 9000000000000 (model13.caps 6)
    (model13.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1170000000000, 9000000000000], [1170000000000,
      9000000000000]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([2625000000000, 0], [5724000000000,
      -9000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next ([2625000000000], [6894000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1455000000000, -9000000000000], [8064000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1170000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-1170000000000, -9000000000000],
      [2340000000000, 18000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-5724000000000,
      9000000000000], [8349000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-6894000000000], [9519000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-8064000000000,
      -9000000000000], [9519000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_7 : ExcludedOn (model13.B 7 ++ [step13.q]) 9000000000000 (model13.caps 7)
    (model13.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_8 : ExcludedOn (model13.B 8 ++ [step13.q]) 9000000000000 (model13.caps 8)
    (model13.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_9 : ExcludedOn (model13.B 9 ++ [step13.q]) 9000000000000 (model13.caps 9)
    (model13.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked13 : StepValid model13 9000000000000 step13 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded13_0
    · exact excluded13_1
    · exact excluded13_2
    · exact excluded13_3
    · exact excluded13_4
    · exact (hj rfl).elim
    · exact excluded13_6
    · exact excluded13_7
    · exact excluded13_8
    · exact excluded13_9
theorem next13 : model13.insert step13 = model14 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded14_0 : ExcludedOn (model14.B 0 ++ [step14.q]) 9000000000000 (model14.caps 0)
    (model14.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5545800000000, 5160000000000], [54600000000,
      -2580000000000]) (some (7, 7, 4)) (some (7, 7, 4)) (.next ([4700400000000, 2580000000000],
      [454200000000, -5160000000000]) (some (7, 7, 4)) (some (7, 7, 4)) (.next ([5210400000000,
      2580000000000], [695400000000, 2580000000000]) (some (7, 7, 4)) (some (7, 7, 4)) (.next
      ([5210400000000, 2580000000000], [725400000000, 2580000000000]) (some (7, 7, 4)) (some (7, 7,
      4)) (.next ([5035800000000, 5160000000000], [789600000000, -2580000000000]) (some (7, 7, 4))
      (some (7, 7, 4)) (.next ([4500000000000], [1095000000000]) (some (7, 7, 4)) (some (7, 7, 4))
      (.next ([4500000000000], [1125000000000]) (some (7, 7, 4)) (some (7, 7, 5)) (.next
      ([4700400000000, 2580000000000], [1460400000000, 2580000000000]) (some (7, 7, 5)) (some (7, 7,
      5)) (.next ([5975400000000, 2580000000000], [2689200000000, -5160000000000]) (some (7, 7, 5))
      (some (7, 7, 5)) (.next ([3990000000000], [1860000000000]) (some (7, 2, 5)) (some (7, 2, 5))
      (.next ([6310800000000, 5160000000000], [3024600000000, -2580000000000]) (some (7, 2, 5))
      (some (7, 2, 5)) (.next ([5304600000000, -2580000000000], [3024600000000, -2580000000000])
      (some (7, 2, 5)) (some (7, 2, 5)) (.next ([6000000000000], [3735000000000]) (some (7, 2, 5))
      (some (7, 2, 5)) (.next ([399600000000, -2580000000000], [310800000000, 5160000000000]) (some
      (7, 2, 5)) (some (7, 2, 5)) (.next ([335400000000, 2580000000000], [335400000000,
      2580000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([695400000000, 2580000000000],
      [710400000000, 2580000000000]) (some (7, 2, 5)) (some (7, 3, 5)) (.next ([255000000000],
      [510000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([225000000000], [510000000000])
      (some (7, 3, 5)) (some (7, 3, 5)) (.next ([310800000000, 5160000000000], [4899600000000,
      -2580000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([280800000000, 5160000000000],
      [4929600000000, -2580000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([405000000000],
      [8235000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([375000000000], [8235000000000])
      (some (7, 3, 5)) (some (7, 3, 5)) (.next ([150000000000], [7725000000000]) (some (7, 3, 5))
      (some (7, 3, 5)) fan14Owner0Part0)))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded14_1 : ExcludedOn (model14.B 1 ++ [step14.q]) 9000000000000 (model14.caps 1)
    (model14.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_2 : ExcludedOn (model14.B 2 ++ [step14.q]) 9000000000000 (model14.caps 2)
    (model14.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_3 : ExcludedOn (model14.B 3 ++ [step14.q]) 9000000000000 (model14.caps 3)
    (model14.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_5 : ExcludedOn (model14.B 5 ++ [step14.q]) 9000000000000 (model14.caps 5)
    (model14.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_6 : ExcludedOn (model14.B 6 ++ [step14.q]) 9000000000000 (model14.caps 6)
    (model14.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_7 : ExcludedOn (model14.B 7 ++ [step14.q]) 9000000000000 (model14.caps 7)
    (model14.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_8 : ExcludedOn (model14.B 8 ++ [step14.q]) 9000000000000 (model14.caps 8)
    (model14.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4470000000000], [2355000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([3360000000000], [5640000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([1185000000000], [2175000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1005000000000], [5640000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [2355000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.next ([-2355000000000], [6825000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-5640000000000], [9000000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-2175000000000], [3360000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-5640000000000], [6645000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded14_9 : ExcludedOn (model14.B 9 ++ [step14.q]) 9000000000000 (model14.caps 9)
    (model14.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked14 : StepValid model14 9000000000000 step14 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded14_0
    · exact excluded14_1
    · exact excluded14_2
    · exact excluded14_3
    · exact (hj rfl).elim
    · exact excluded14_5
    · exact excluded14_6
    · exact excluded14_7
    · exact excluded14_8
    · exact excluded14_9
theorem next14 : model14.insert step14 = model15 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded15_0 : ExcludedOn (model15.B 0 ++ [step15.q]) 9000000000000 (model15.caps 0)
    (model15.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5545800000000, 5160000000000], [54600000000,
      -2580000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([4700400000000, 2580000000000],
      [454200000000, -5160000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([5210400000000,
      2580000000000], [695400000000, 2580000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
      ([5210400000000, 2580000000000], [725400000000, 2580000000000]) (some (0, 7, 4)) (some (0, 7,
      4)) (.next ([5035800000000, 5160000000000], [789600000000, -2580000000000]) (some (0, 7, 4))
      (some (0, 7, 4)) (.next ([4500000000000], [1095000000000]) (some (0, 7, 4)) (some (0, 7, 4))
      (.next ([4500000000000], [1125000000000]) (some (0, 7, 4)) (some (0, 7, 5)) (.next
      ([4700400000000, 2580000000000], [1460400000000, 2580000000000]) (some (0, 7, 5)) (some (0, 7,
      5)) (.next ([3990000000000], [1860000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
      ([5475000000000], [4650000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([5445000000000],
      [4680000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([335400000000, 2580000000000],
      [335400000000, 2580000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([695400000000,
      2580000000000], [710400000000, 2580000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
      ([4710000000000], [4905000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([255000000000],
      [510000000000]) (some (0, 7, 5)) (some (7, 7, 5)) (.next ([225000000000], [510000000000])
      (some (7, 7, 5)) (some (7, 7, 5)) (.next ([1255800000000, 5160000000000], [4914600000000,
      -2580000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([920400000000, 2580000000000],
      [4579200000000, -5160000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([945000000000],
      [5625000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([310800000000, 5160000000000],
      [4899600000000, -2580000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([280800000000,
      5160000000000], [4929600000000, -2580000000000]) (some (7, 3, 5)) (some (7, 3, 5))
      fan15Owner0Part0)))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded15_1 : ExcludedOn (model15.B 1 ++ [step15.q]) 9000000000000 (model15.caps 1)
    (model15.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_2 : ExcludedOn (model15.B 2 ++ [step15.q]) 9000000000000 (model15.caps 2)
    (model15.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_3 : ExcludedOn (model15.B 3 ++ [step15.q]) 9000000000000 (model15.caps 3)
    (model15.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_5 : ExcludedOn (model15.B 5 ++ [step15.q]) 9000000000000 (model15.caps 5)
    (model15.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2106000000000], [519000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) fan15Owner5Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded15_6 : ExcludedOn (model15.B 6 ++ [step15.q]) 9000000000000 (model15.caps 6)
    (model15.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_7 : ExcludedOn (model15.B 7 ++ [step15.q]) 9000000000000 (model15.caps 7)
    (model15.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_8 : ExcludedOn (model15.B 8 ++ [step15.q]) 9000000000000 (model15.caps 8)
    (model15.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_9 : ExcludedOn (model15.B 9 ++ [step15.q]) 9000000000000 (model15.caps 9)
    (model15.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked15 : StepValid model15 9000000000000 step15 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded15_0
    · exact excluded15_1
    · exact excluded15_2
    · exact excluded15_3
    · exact (hj rfl).elim
    · exact excluded15_5
    · exact excluded15_6
    · exact excluded15_7
    · exact excluded15_8
    · exact excluded15_9
theorem next15 : model15.insert step15 = model16 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint130000140000
end ConwaySoifer.Simplified.Certificates
