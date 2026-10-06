/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint260000270000
import Mathlib.Tactic.FinCases

/-!
# Sint 260000 270000 1

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
namespace Sint260000270000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan13Owner0Part0 : FanWitness := (.next ([-343800000000, -4380000000000], [944400000000,
    2190000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-944400000000, -2190000000000],
    [2308800000000, 4380000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-180000000000],
    [405000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-4875000000000], [10242000000000])
    (some (10, 3, 6)) (some (10, 3, 7)) (.next ([-1170000000000], [2340000000000]) (some (10, 3, 7))
    (some (10, 3, 7)) (.next ([-4875000000000], [9702000000000]) (some (10, 3, 7)) (some (10, 4, 7))
    (.next ([-5100000000000], [10062000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-763800000000, -4380000000000], [1364400000000, 2190000000000]) (some (10, 4, 7)) (some (10,
    4, 7)) (.next ([-1364400000000, -2190000000000], [2308800000000, 4380000000000]) (some (10, 4,
    7)) (some (10, 4, 7)) (.next ([-600600000000, 2190000000000], [944400000000, 2190000000000])
    (some (10, 4, 7)) (some (10, 4, 7)) (.next ([-1590000000000], [2340000000000]) (some (10, 4, 7))
    (some (10, 4, 7)) (.next ([-3417000000000], [4962000000000]) (some (10, 4, 7)) (some (10, 4, 7))
    (.next ([-4680600000000, 2190000000000], [6599400000000, 2190000000000]) (some (10, 4, 7)) (some
    (10, 4, 7)) (.next ([-3837000000000], [5382000000000]) (some (10, 4, 7)) (some (10, 4, 7))
    (.next ([-4875000000000], [6825000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-4905600000000, 2190000000000], [6419400000000, 2190000000000]) (some (10, 4, 7)) (some (10,
    4, 7)) (.next ([-5100000000000], [6645000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-4875000000000], [6285000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-4587000000000], [5757000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next ([-5819400000000,
    -2190000000000], [7168800000000, 4380000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-6044400000000, -2190000000000], [6988800000000, 4380000000000]) (some (10, 4, 7)) (some (10,
    4, 7)) (.next ([-5007000000000], [5757000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-5819400000000, -2190000000000], [6628800000000, 4380000000000]) (some (10, 4, 7)) (some (10,
    4, 7)) (.next ([-6420000000000], [6825000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.terminal
    (some (10, 4, 7)) (some (10, 4, 7)) (some (10, 4, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan13Owner0Part1 : FanWitness := (.next ([1513800000000, 4380000000000], [4905600000000,
    -2190000000000]) (some (10, 2, 6)) (some (10, 2, 6)) (.next ([1545000000000], [5100000000000])
    (some (10, 2, 6)) (some (10, 2, 6)) (.next ([1410000000000], [4875000000000]) (some (10, 2, 6))
    (some (10, 2, 6)) (.next ([1170000000000], [4587000000000]) (some (10, 2, 6)) (some (10, 2, 6))
    (.next ([1349400000000, 2190000000000], [5819400000000, 2190000000000]) (some (10, 2, 6)) (some
    (10, 2, 6)) (.next ([944400000000, 2190000000000], [6044400000000, 2190000000000]) (some (10, 2,
    6)) (some (10, 2, 6)) (.next ([750000000000], [5007000000000]) (some (10, 2, 6)) (some (10, 2,
    6)) (.next ([809400000000, 2190000000000], [5819400000000, 2190000000000]) (some (10, 2, 6))
    (some (10, 2, 6)) (.next ([405000000000], [6420000000000]) (some (10, 2, 6)) (some (10, 2, 6))
    (.next ([0], [1545000000000]) (some (10, 2, 6)) (some (10, 2, 6)) (.next ([-15000000000],
    [6420000000000]) (some (10, 2, 6)) (some (10, 3, 6)) (.next ([-135000000000], [6420000000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-194400000000, -2190000000000], [3642600000000,
    -2190000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-420000000000], [6645000000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-390000000000], [6045000000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-390000000000], [5625000000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-555000000000], [6420000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-194400000000, -2190000000000], [1933800000000, 4380000000000]) (some (10, 3, 6)) (some (10,
    3, 6)) (.next ([-795000000000], [6270000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-795000000000], [5850000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-930000000000],
    [6045000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-930000000000], [5625000000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-420000000000], [1965000000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-375000000000], [1170000000000]) (some (10, 3, 6)) (some (10, 3, 6))
    fan13Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan13Owner0Part2 : FanWitness := (.next ([5235000000000], [390000000000]) (some (7, 10, 5))
    (some (7, 10, 5)) (.next ([5865000000000], [555000000000]) (some (7, 10, 5)) (some (7, 10, 6))
    (.next ([1739400000000, 2190000000000], [194400000000, 2190000000000]) (some (7, 10, 6)) (some
    (7, 10, 6)) (.next ([5475000000000], [795000000000]) (some (7, 10, 6)) (some (7, 10, 6)) (.next
    ([5055000000000], [795000000000]) (some (7, 10, 6)) (some (7, 10, 6)) (.next ([5115000000000],
    [930000000000]) (some (7, 10, 6)) (some (7, 10, 6)) (.next ([4695000000000], [930000000000])
    (some (7, 10, 6)) (some (7, 10, 6)) (.next ([1545000000000], [420000000000]) (some (7, 10, 6))
    (some (7, 10, 6)) (.next ([795000000000], [375000000000]) (some (7, 10, 6)) (some (7, 10, 6))
    (.next ([600600000000, -2190000000000], [343800000000, 4380000000000]) (some (7, 10, 6)) (some
    (7, 10, 6)) (.next ([1364400000000, 2190000000000], [944400000000, 2190000000000]) (some (7, 10,
    6)) (some (7, 10, 6)) (.next ([225000000000], [180000000000]) (some (7, 10, 6)) (some (7, 10,
    6)) (.next ([5367000000000], [4875000000000]) (some (7, 10, 6)) (some (7, 10, 6)) (.next
    ([1170000000000], [1170000000000]) (some (7, 10, 6)) (some (7, 10, 6)) (.next ([4827000000000],
    [4875000000000]) (some (7, 10, 6)) (some (7, 10, 6)) (.next ([4962000000000], [5100000000000])
    (some (7, 10, 6)) (some (7, 10, 6)) (.next ([600600000000, -2190000000000], [763800000000,
    4380000000000]) (some (7, 10, 6)) (some (10, 10, 6)) (.next ([944400000000, 2190000000000],
    [1364400000000, 2190000000000]) (some (10, 10, 6)) (some (10, 10, 6)) (.next ([343800000000,
    4380000000000], [600600000000, -2190000000000]) (some (10, 10, 6)) (some (10, 10, 6)) (.next
    ([750000000000], [1590000000000]) (some (10, 10, 6)) (some (10, 10, 6)) (.next ([1545000000000],
    [3417000000000]) (some (10, 10, 6)) (some (10, 10, 6)) (.next ([1918800000000, 4380000000000],
    [4680600000000, -2190000000000]) (some (10, 2, 6)) (some (10, 2, 6)) (.next ([1545000000000],
    [3837000000000]) (some (10, 2, 6)) (some (10, 2, 6)) (.next ([1950000000000], [4875000000000])
    (some (10, 2, 6)) (some (10, 2, 6)) fan13Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner0Part0 : FanWitness := (.next ([-2667000000000], [8250000000000]) (some (10, 3, 10))
    (some (10, 3, 10)) (.next ([-2698200000000, 4380000000000], [8055600000000, -2190000000000])
    (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-3267600000000, 2190000000000], [9194400000000,
    2190000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-343800000000, -4380000000000],
    [944400000000, 2190000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-944400000000,
    -2190000000000], [2308800000000, 4380000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next
    ([-4212000000000], [9795000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-180000000000],
    [405000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-4632000000000], [9795000000000])
    (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-1170000000000], [2340000000000]) (some (0, 3, 10))
    (some (0, 3, 10)) (.next ([-5007000000000], [9420000000000]) (some (0, 3, 10)) (some (0, 4, 10))
    (.next ([-5007000000000], [9000000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([-763800000000, -4380000000000], [1364400000000, 2190000000000]) (some (0, 4, 10)) (some (0, 4,
    10)) (.next ([-1364400000000, -2190000000000], [2308800000000, 4380000000000]) (some (0, 4, 10))
    (some (0, 4, 10)) (.next ([-600600000000, 2190000000000], [944400000000, 2190000000000]) (some
    (0, 4, 10)) (some (0, 4, 10)) (.next ([-1590000000000], [2340000000000]) (some (0, 4, 10)) (some
    (1, 4, 10)) (.next ([-4680600000000, 2190000000000], [6599400000000, 2190000000000]) (some (1,
    4, 10)) (some (1, 4, 10)) (.next ([-4875000000000], [6825000000000]) (some (1, 4, 10)) (some (1,
    4, 10)) (.next ([-4905600000000, 2190000000000], [6419400000000, 2190000000000]) (some (1, 4,
    10)) (some (1, 4, 10)) (.next ([-5100000000000], [6645000000000]) (some (1, 4, 10)) (some (1, 4,
    10)) (.next ([-4875000000000], [6285000000000]) (some (1, 4, 10)) (some (1, 4, 10)) (.next
    ([-5819400000000, -2190000000000], [7168800000000, 4380000000000]) (some (1, 4, 10)) (some (1,
    4, 10)) (.next ([-6044400000000, -2190000000000], [6988800000000, 4380000000000]) (some (1, 4,
    10)) (some (1, 4, 10)) (.next ([-5819400000000, -2190000000000], [6628800000000, 4380000000000])
    (some (1, 4, 10)) (some (1, 4, 10)) (.next ([-6420000000000], [6825000000000]) (some (1, 4, 10))
    (some (1, 4, 10)) (.terminal (some (1, 4, 10)) (some (1, 4, 10)) (some (1, 4,
    10)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner0Part1 : FanWitness := (.next ([1513800000000, 4380000000000], [4905600000000,
    -2190000000000]) (some (10, 2, 6)) (some (10, 2, 6)) (.next ([1545000000000], [5100000000000])
    (some (10, 2, 6)) (some (10, 2, 6)) (.next ([1410000000000], [4875000000000]) (some (10, 2, 6))
    (some (10, 2, 6)) (.next ([1349400000000, 2190000000000], [5819400000000, 2190000000000]) (some
    (10, 2, 6)) (some (10, 2, 6)) (.next ([944400000000, 2190000000000], [6044400000000,
    2190000000000]) (some (10, 2, 6)) (some (10, 2, 6)) (.next ([809400000000, 2190000000000],
    [5819400000000, 2190000000000]) (some (10, 2, 6)) (some (10, 2, 6)) (.next ([405000000000],
    [6420000000000]) (some (10, 2, 6)) (some (10, 2, 6)) (.next ([0], [1545000000000]) (some (10, 2,
    6)) (some (10, 2, 6)) (.next ([-15000000000], [6420000000000]) (some (10, 2, 6)) (some (10, 3,
    6)) (.next ([-135000000000], [6420000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-420000000000], [6645000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-390000000000],
    [6045000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-390000000000], [5625000000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-555000000000], [6420000000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-194400000000, -2190000000000], [1933800000000, 4380000000000]) (some
    (10, 3, 6)) (some (10, 3, 6)) (.next ([-795000000000], [6270000000000]) (some (10, 3, 6)) (some
    (10, 3, 6)) (.next ([-795000000000], [5850000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-930000000000], [6045000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-930000000000],
    [5625000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-702000000000], [4077000000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-420000000000], [1965000000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-1062000000000], [4212000000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-1242000000000], [4617000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-375000000000], [1170000000000]) (some (10, 3, 6)) (some (10, 3, 10))
    fan14Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner0Part2 : FanWitness := (.next ([5115000000000], [930000000000]) (some (10, 1, 6))
    (some (10, 1, 6)) (.next ([4695000000000], [930000000000]) (some (10, 1, 6)) (some (10, 1, 6))
    (.next ([3375000000000], [702000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next
    ([1545000000000], [420000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next ([3150000000000],
    [1062000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next ([3375000000000], [1242000000000])
    (some (10, 1, 6)) (some (10, 1, 6)) (.next ([795000000000], [375000000000]) (some (10, 1, 6))
    (some (10, 1, 6)) (.next ([5583000000000], [2667000000000]) (some (10, 1, 6)) (some (10, 1, 6))
    (.next ([5357400000000, 2190000000000], [2698200000000, -4380000000000]) (some (10, 1, 6)) (some
    (10, 1, 6)) (.next ([5926800000000, 4380000000000], [3267600000000, -2190000000000]) (some (10,
    1, 6)) (some (10, 1, 6)) (.next ([600600000000, -2190000000000], [343800000000, 4380000000000])
    (some (10, 1, 6)) (some (10, 1, 6)) (.next ([1364400000000, 2190000000000], [944400000000,
    2190000000000]) (some (10, 1, 6)) (some (10, 2, 6)) (.next ([5583000000000], [4212000000000])
    (some (10, 2, 6)) (some (10, 2, 6)) (.next ([225000000000], [180000000000]) (some (10, 2, 6))
    (some (10, 2, 6)) (.next ([5163000000000], [4632000000000]) (some (10, 2, 6)) (some (10, 2, 6))
    (.next ([1170000000000], [1170000000000]) (some (10, 2, 6)) (some (10, 2, 6)) (.next
    ([4413000000000], [5007000000000]) (some (10, 2, 6)) (some (10, 2, 6)) (.next ([3993000000000],
    [5007000000000]) (some (10, 2, 6)) (some (10, 2, 6)) (.next ([600600000000, -2190000000000],
    [763800000000, 4380000000000]) (some (10, 2, 6)) (some (10, 2, 6)) (.next ([944400000000,
    2190000000000], [1364400000000, 2190000000000]) (some (10, 2, 6)) (some (10, 2, 6)) (.next
    ([343800000000, 4380000000000], [600600000000, -2190000000000]) (some (10, 2, 6)) (some (10, 2,
    6)) (.next ([750000000000], [1590000000000]) (some (10, 2, 6)) (some (10, 2, 6)) (.next
    ([1918800000000, 4380000000000], [4680600000000, -2190000000000]) (some (10, 2, 6)) (some (10,
    2, 6)) (.next ([1950000000000], [4875000000000]) (some (10, 2, 6)) (some (10, 2, 6))
    fan14Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner0Part0 : FanWitness := (.next ([-1138800000000, -4380000000000], [3074400000000,
    2190000000000]) (some (0, 10, 6)) (some (0, 10, 6)) (.next ([-1170000000000], [2880000000000])
    (some (0, 10, 6)) (some (0, 10, 6)) (.next ([-944400000000, -2190000000000], [2308800000000,
    4380000000000]) (some (0, 10, 6)) (some (10, 10, 6)) (.next ([-180000000000], [405000000000])
    (some (10, 10, 6)) (some (10, 10, 6)) (.next ([-1170000000000], [2340000000000]) (some (10, 10,
    6)) (some (10, 10, 7)) (.next ([-763800000000, -4380000000000], [1364400000000, 2190000000000])
    (some (10, 10, 7)) (some (10, 10, 7)) (.next ([-1364400000000, -2190000000000], [2308800000000,
    4380000000000]) (some (10, 10, 7)) (some (10, 10, 7)) (.next ([-1710000000000], [2880000000000])
    (some (10, 10, 7)) (some (10, 10, 7)) (.next ([-600600000000, 2190000000000], [944400000000,
    2190000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next ([-2130000000000], [3300000000000])
    (some (10, 4, 7)) (some (10, 4, 7)) (.next ([-1590000000000], [2340000000000]) (some (10, 4, 7))
    (some (10, 4, 7)) (.next ([-4680600000000, 2190000000000], [6599400000000, 2190000000000]) (some
    (10, 4, 7)) (some (10, 4, 7)) (.next ([-4875000000000], [6825000000000]) (some (10, 4, 7)) (some
    (10, 4, 7)) (.next ([-4905600000000, 2190000000000], [6419400000000, 2190000000000]) (some (10,
    4, 7)) (some (10, 4, 7)) (.next ([-5100000000000], [6645000000000]) (some (10, 4, 7)) (some (10,
    4, 7)) (.next ([-4875000000000], [6285000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-1335000000000], [1710000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next ([-5819400000000,
    -2190000000000], [7168800000000, 4380000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-6044400000000, -2190000000000], [6988800000000, 4380000000000]) (some (10, 4, 7)) (some (10,
    4, 7)) (.next ([-5819400000000, -2190000000000], [6628800000000, 4380000000000]) (some (10, 4,
    7)) (some (10, 4, 7)) (.next ([-7755000000000], [8535000000000]) (some (10, 4, 7)) (some (10, 4,
    7)) (.next ([-6420000000000], [6825000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-7980000000000], [8355000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-7755000000000], [7995000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.terminal (some (10, 4,
    7)) (some (10, 4, 7)) (some (10, 4, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner0Part1 : FanWitness := (.next ([1410000000000], [4875000000000]) (some (8, 10, 6))
    (some (9, 10, 6)) (.next ([375000000000], [1335000000000]) (some (9, 10, 6)) (some (9, 10, 6))
    (.next ([1349400000000, 2190000000000], [5819400000000, 2190000000000]) (some (9, 10, 6)) (some
    (9, 10, 6)) (.next ([944400000000, 2190000000000], [6044400000000, 2190000000000]) (some (9, 10,
    6)) (some (9, 10, 6)) (.next ([809400000000, 2190000000000], [5819400000000, 2190000000000])
    (some (9, 10, 6)) (some (9, 10, 6)) (.next ([780000000000], [7755000000000]) (some (9, 10, 6))
    (some (9, 10, 6)) (.next ([405000000000], [6420000000000]) (some (9, 10, 6)) (some (9, 10, 6))
    (.next ([375000000000], [7980000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next
    ([240000000000], [7755000000000]) (some (9, 10, 6)) (some (0, 10, 6)) (.next ([0],
    [1545000000000]) (some (0, 10, 6)) (some (0, 10, 6)) (.next ([-15000000000], [6420000000000])
    (some (0, 10, 6)) (some (0, 10, 6)) (.next ([-135000000000], [6420000000000]) (some (0, 10, 6))
    (some (0, 10, 6)) (.next ([-420000000000], [6645000000000]) (some (0, 10, 6)) (some (0, 10, 6))
    (.next ([-390000000000], [6045000000000]) (some (0, 10, 6)) (some (0, 10, 6)) (.next
    ([-390000000000], [5625000000000]) (some (0, 10, 6)) (some (0, 10, 6)) (.next ([-555000000000],
    [6420000000000]) (some (0, 10, 6)) (some (0, 10, 6)) (.next ([-194400000000, -2190000000000],
    [1933800000000, 4380000000000]) (some (0, 10, 6)) (some (0, 10, 6)) (.next ([-795000000000],
    [6270000000000]) (some (0, 10, 6)) (some (0, 10, 6)) (.next ([-795000000000], [5850000000000])
    (some (0, 10, 6)) (some (0, 10, 6)) (.next ([-930000000000], [6045000000000]) (some (0, 10, 6))
    (some (0, 10, 6)) (.next ([-930000000000], [5625000000000]) (some (0, 10, 6)) (some (0, 10, 6))
    (.next ([-420000000000], [1965000000000]) (some (0, 10, 6)) (some (0, 10, 6)) (.next
    ([-569400000000, -2190000000000], [1935600000000, -2190000000000]) (some (0, 10, 6)) (some (0,
    10, 6)) (.next ([-375000000000], [1170000000000]) (some (0, 10, 6)) (some (0, 10, 6))
    fan15Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner0Part2 : FanWitness := (.next ([5865000000000], [555000000000]) (some (7, 10, 5))
    (some (7, 10, 6)) (.next ([1739400000000, 2190000000000], [194400000000, 2190000000000]) (some
    (7, 10, 6)) (some (7, 10, 6)) (.next ([5475000000000], [795000000000]) (some (7, 10, 6)) (some
    (7, 10, 6)) (.next ([5055000000000], [795000000000]) (some (7, 10, 6)) (some (7, 10, 6)) (.next
    ([5115000000000], [930000000000]) (some (7, 10, 6)) (some (7, 10, 6)) (.next ([4695000000000],
    [930000000000]) (some (7, 10, 6)) (some (7, 10, 6)) (.next ([1545000000000], [420000000000])
    (some (7, 10, 6)) (some (7, 10, 6)) (.next ([1366200000000, -4380000000000], [569400000000,
    2190000000000]) (some (7, 10, 6)) (some (7, 10, 6)) (.next ([795000000000], [375000000000])
    (some (7, 10, 6)) (some (7, 10, 6)) (.next ([1935600000000, -2190000000000], [1138800000000,
    4380000000000]) (some (7, 10, 6)) (some (7, 10, 6)) (.next ([1710000000000], [1170000000000])
    (some (7, 10, 6)) (some (7, 10, 6)) (.next ([1364400000000, 2190000000000], [944400000000,
    2190000000000]) (some (7, 10, 6)) (some (7, 10, 6)) (.next ([225000000000], [180000000000])
    (some (7, 10, 6)) (some (7, 10, 6)) (.next ([1170000000000], [1170000000000]) (some (7, 10, 6))
    (some (7, 10, 6)) (.next ([600600000000, -2190000000000], [763800000000, 4380000000000]) (some
    (7, 10, 6)) (some (7, 10, 6)) (.next ([944400000000, 2190000000000], [1364400000000,
    2190000000000]) (some (7, 10, 6)) (some (7, 10, 6)) (.next ([1170000000000], [1710000000000])
    (some (7, 10, 6)) (some (7, 10, 6)) (.next ([343800000000, 4380000000000], [600600000000,
    -2190000000000]) (some (7, 10, 6)) (some (7, 10, 6)) (.next ([1170000000000], [2130000000000])
    (some (7, 10, 6)) (some (8, 10, 6)) (.next ([750000000000], [1590000000000]) (some (8, 10, 6))
    (some (8, 10, 6)) (.next ([1918800000000, 4380000000000], [4680600000000, -2190000000000]) (some
    (8, 10, 6)) (some (8, 10, 6)) (.next ([1950000000000], [4875000000000]) (some (8, 10, 6)) (some
    (8, 10, 6)) (.next ([1513800000000, 4380000000000], [4905600000000, -2190000000000]) (some (8,
    10, 6)) (some (8, 10, 6)) (.next ([1545000000000], [5100000000000]) (some (8, 10, 6)) (some (8,
    10, 6)) fan15Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner4Part0 : FanWitness := (.next ([1965000000000, 9000000000000], [2448000000000,
    -9000000000000]) (some (4, 1, 6)) (some (5, 1, 6)) (.next ([2073000000000, -9000000000000],
    [2715000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2505000000000],
    [6495000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([750000000000], [3150000000000])
    (some (5, 1, 6)) (some (5, 1, 6)) (.next ([630000000000], [3120000000000]) (some (5, 1, 6))
    (some (5, 1, 6)) (.next ([165000000000, -9000000000000], [6495000000000, 0]) (some (5, 1, 6))
    (some (5, 1, 6)) (.next ([0, 0], [2340000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 6,
    6)) (.next ([-375000000000], [4788000000000]) (some (0, 6, 6)) (some (0, 6, 6)) (.next
    ([-30000000000], [150000000000]) (some (0, 6, 6)) (some (0, 6, 6)) (.next ([-888000000000],
    [3663000000000]) (some (0, 6, 6)) (some (0, 6, 6)) (.next ([-1038000000000], [3783000000000])
    (some (0, 6, 6)) (some (0, 6, 6)) (.next ([-1590000000000, -9000000000000], [5490000000000,
    9000000000000]) (some (0, 6, 6)) (some (0, 6, 6)) (.next ([-2595000000000], [8250000000000])
    (some (0, 6, 6)) (some (0, 6, 6)) (.next ([-2745000000000], [8370000000000]) (some (0, 6, 3))
    (some (0, 6, 3)) (.next ([-1707000000000], [4587000000000]) (some (0, 6, 3)) (some (0, 6, 3))
    (.next ([-4155000000000, 9000000000000], [9000000000000]) (some (0, 6, 3)) (some (0, 6, 3))
    (.next ([-2340000000000, -9000000000000], [4680000000000, 18000000000000]) (some (0, 6, 3))
    (some (0, 6, 3)) (.next ([-780000000000, 9000000000000], [1410000000000, -9000000000000]) (some
    (0, 6, 3)) (some (0, 6, 3)) (.next ([-2448000000000, 9000000000000], [4413000000000]) (some (0,
    6, 3)) (some (0, 6, 3)) (.next ([-2715000000000, -9000000000000], [4788000000000, 0]) (some (0,
    6, 3)) (some (0, 6, 3)) (.next ([-6495000000000], [9000000000000]) (some (0, 6, 3)) (some (0, 6,
    3)) (.next ([-3150000000000], [3900000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next
    ([-3120000000000], [3750000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([-6495000000000,
    0], [6660000000000, -9000000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.terminal (some (0, 6,
    3)) (some (0, 6, 3)) (some (0, 6, 3)))))))))))))))))))))))))))

theorem excluded8_1 : ExcludedOn (model8.B 1 ++ [step8.q]) 9000000000000 (model8.caps 1) (model8.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7830000000000], [795000000000]) (some (0, 3, 1))
      (some (0, 3, 2)) (.next ([5490000000000, -9000000000000], [3135000000000, 9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([2340000000000, 9000000000000], [2340000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([1545000000000, 9000000000000],
      [6285000000000, -9000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next ([0, 0],
      [2340000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-795000000000],
      [8625000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-3135000000000, -9000000000000],
      [8625000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2340000000000,
      -9000000000000], [4680000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-6285000000000, 9000000000000], [7830000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_2 : ExcludedOn (model8.B 2 ++ [step8.q]) 9000000000000 (model8.caps 2) (model8.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_3 : ExcludedOn (model8.B 3 ++ [step8.q]) 9000000000000 (model8.caps 3) (model8.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_4 : ExcludedOn (model8.B 4 ++ [step8.q]) 9000000000000 (model8.caps 4) (model8.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_5 : ExcludedOn (model8.B 5 ++ [step8.q]) 9000000000000 (model8.caps 5) (model8.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7035000000000, -9000000000000], [1170000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([2340000000000, 9000000000000],
      [2340000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([3510000000000,
      9000000000000], [5865000000000, -9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next
      ([1170000000000], [8205000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0],
      [2340000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1170000000000,
      -9000000000000], [8205000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-2340000000000,
      -9000000000000], [4680000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-5865000000000, 9000000000000], [9375000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-8205000000000], [9375000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_6 : ExcludedOn (model8.B 6 ++ [step8.q]) 9000000000000 (model8.caps 6) (model8.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5865000000000, -9000000000000], [1965000000000,
      9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([2340000000000, 9000000000000],
      [2340000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2715000000000,
      9000000000000], [5490000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([375000000000], [7830000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [2340000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-1965000000000,
      -9000000000000], [7830000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-2340000000000,
      -9000000000000], [4680000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next
      ([-5490000000000, 9000000000000], [8205000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next
      ([-7830000000000], [8205000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1,
      3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded8_1
    · exact excluded8_2
    · exact excluded8_3
    · exact excluded8_4
    · exact excluded8_5
    · exact excluded8_6
    · exact excluded8_7
    · exact excluded8_8
    · exact excluded8_9
theorem next8 : model8.insert step8 = model9 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded9_1 : ExcludedOn (model9.B 1 ++ [step9.q]) 9000000000000 (model9.caps 1) (model9.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7830000000000], [375000000000]) (some (0, 3, 1))
      (some (0, 3, 2)) (.next ([5490000000000, -9000000000000], [2715000000000, 9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([2340000000000, 9000000000000], [2340000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([1965000000000, 9000000000000],
      [5865000000000, -9000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next ([0, 0],
      [2340000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-375000000000],
      [8205000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2715000000000, -9000000000000],
      [8205000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2340000000000,
      -9000000000000], [4680000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-5865000000000, 9000000000000], [7830000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_2 : ExcludedOn (model9.B 2 ++ [step9.q]) 9000000000000 (model9.caps 2) (model9.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8205000000000], [1170000000000]) (some (0, 3,
      1)) (some (0, 3, 1)) (.next ([6660000000000, -9000000000000], [2340000000000, 9000000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([5490000000000, -9000000000000], [2715000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([5865000000000, -9000000000000],
      [3510000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0, 0],
      [2340000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-1170000000000],
      [9375000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([-2340000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-2715000000000,
      -9000000000000], [8205000000000, 0]) (some (0, 3, 2)) (some (0, 3, 2)) (.next
      ([-3510000000000, -9000000000000], [9375000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.terminal (some (0, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_3 : ExcludedOn (model9.B 3 ++ [step9.q]) 9000000000000 (model9.caps 3) (model9.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_4 : ExcludedOn (model9.B 4 ++ [step9.q]) 9000000000000 (model9.caps 4) (model9.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_5 : ExcludedOn (model9.B 5 ++ [step9.q]) 9000000000000 (model9.caps 5) (model9.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_6 : ExcludedOn (model9.B 6 ++ [step9.q]) 9000000000000 (model9.caps 6) (model9.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6285000000000, -9000000000000], [1545000000000,
      9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([2340000000000, 9000000000000],
      [2340000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([3135000000000,
      9000000000000], [5490000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([795000000000], [7830000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [2340000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-1545000000000,
      -9000000000000], [7830000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-2340000000000,
      -9000000000000], [4680000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next
      ([-5490000000000, 9000000000000], [8625000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next
      ([-7830000000000], [8625000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1,
      3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_7 : ExcludedOn (model9.B 7 ++ [step9.q]) 9000000000000 (model9.caps 7) (model9.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_8 : ExcludedOn (model9.B 8 ++ [step9.q]) 9000000000000 (model9.caps 8) (model9.ord
    8) 0 1 100 := by
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
    · exact (hj rfl).elim
    · exact excluded9_1
    · exact excluded9_2
    · exact excluded9_3
    · exact excluded9_4
    · exact excluded9_5
    · exact excluded9_6
    · exact excluded9_7
    · exact excluded9_8
    · exact excluded9_9
theorem next9 : model9.insert step9 = model10 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded10_0 : ExcludedOn (model10.B 0 ++ [step10.q]) 9000000000000 (model10.caps 0)
    (model10.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_1 : ExcludedOn (model10.B 1 ++ [step10.q]) 9000000000000 (model10.caps 1)
    (model10.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_2 : ExcludedOn (model10.B 2 ++ [step10.q]) 9000000000000 (model10.caps 2)
    (model10.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_3 : ExcludedOn (model10.B 3 ++ [step10.q]) 9000000000000 (model10.caps 3)
    (model10.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_4 : ExcludedOn (model10.B 4 ++ [step10.q]) 9000000000000 (model10.caps 4)
    (model10.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded10_3
    · exact excluded10_4
    · exact excluded10_5
    · exact excluded10_6
    · exact excluded10_7
    · exact (hj rfl).elim
    · exact excluded10_9
theorem next10 : model10.insert step10 = model11 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded11_0 : ExcludedOn (model11.B 0 ++ [step11.q]) 9000000000000 (model11.caps 0)
    (model11.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_5 : ExcludedOn (model11.B 5 ++ [step11.q]) 9000000000000 (model11.caps 5)
    (model11.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_6 : ExcludedOn (model11.B 6 ++ [step11.q]) 9000000000000 (model11.caps 6)
    (model11.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_7 : ExcludedOn (model11.B 7 ++ [step11.q]) 9000000000000 (model11.caps 7)
    (model11.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_8 : ExcludedOn (model11.B 8 ++ [step11.q]) 9000000000000 (model11.caps 8)
    (model11.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5880000000000], [3750000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([2925000000000, -9000000000000], [2340000000000, 9000000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([3540000000000, -9000000000000], [3750000000000, 0])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1515000000000], [4365000000000]) (some (0, 1, 3))
      (some (0, 3, 3)) (.next ([0, 0], [2340000000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3,
      2)) (.next ([-3750000000000], [9630000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next
      ([-2340000000000, -9000000000000], [5265000000000, 0]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-3750000000000, 0], [7290000000000, -9000000000000]) (some (0, 3, 2)) (some (0, 3,
      2)) (.next ([-4365000000000], [5880000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal
      (some (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded11_5
    · exact excluded11_6
    · exact excluded11_7
    · exact excluded11_8
    · exact excluded11_9
theorem next11 : model11.insert step11 = model12 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded12_0 : ExcludedOn (model12.B 0 ++ [step12.q]) 9000000000000 (model12.caps 0)
    (model12.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_5 : ExcludedOn (model12.B 5 ++ [step12.q]) 9000000000000 (model12.caps 5)
    (model12.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_6 : ExcludedOn (model12.B 6 ++ [step12.q]) 9000000000000 (model12.caps 6)
    (model12.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_7 : ExcludedOn (model12.B 7 ++ [step12.q]) 9000000000000 (model12.caps 7)
    (model12.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_8 : ExcludedOn (model12.B 8 ++ [step12.q]) 9000000000000 (model12.caps 8)
    (model12.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5850000000000], [3900000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([2925000000000, -9000000000000], [2340000000000, 9000000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([3510000000000, -9000000000000], [3900000000000, 0])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1365000000000], [4485000000000]) (some (0, 1, 3))
      (some (0, 3, 3)) (.next ([0, 0], [2340000000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3,
      2)) (.next ([-3900000000000], [9750000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next
      ([-2340000000000, -9000000000000], [5265000000000, 0]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-3900000000000, 0], [7410000000000, -9000000000000]) (some (0, 3, 2)) (some (0, 3,
      2)) (.next ([-4485000000000], [5850000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal
      (some (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded12_5
    · exact excluded12_6
    · exact excluded12_7
    · exact excluded12_8
    · exact excluded12_9
theorem next12 : model12.insert step12 = model13 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded13_0 : ExcludedOn (model13.B 0 ++ [step13.q]) 9000000000000 (model13.caps 0)
    (model13.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6405000000000], [15000000000]) (some (7, 10, 4))
      (some (7, 10, 5)) (.next ([6285000000000], [135000000000]) (some (7, 10, 5)) (some (7, 10, 5))
      (.next ([3448200000000, -4380000000000], [194400000000, 2190000000000]) (some (7, 10, 5))
      (some (7, 10, 5)) (.next ([6225000000000], [420000000000]) (some (7, 10, 5)) (some (7, 10, 5))
      (.next ([5655000000000], [390000000000]) (some (7, 10, 5)) (some (7, 10, 5))
      fan13Owner0Part2)))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_5 : ExcludedOn (model13.B 5 ++ [step13.q]) 9000000000000 (model13.caps 5)
    (model13.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4788000000000, 0], [2247000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([4788000000000], [4587000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2340000000000, 9000000000000], [2340000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2448000000000, -9000000000000],
      [6927000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [2340000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-2247000000000,
      9000000000000], [7035000000000, -9000000000000]) (some (3, 1, 3)) (some (3, 2, 3)) (.next
      ([-4587000000000], [9375000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2340000000000,
      -9000000000000], [4680000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-6927000000000, -9000000000000], [9375000000000]) (some (0, 2, 3)) (some (0, 2, 3))
      (.terminal (some (0, 2, 3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_6 : ExcludedOn (model13.B 6 ++ [step13.q]) 9000000000000 (model13.caps 6)
    (model13.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded13_5
    · exact excluded13_6
    · exact excluded13_7
    · exact excluded13_8
    · exact excluded13_9
theorem next13 : model13.insert step13 = model14 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded14_0 : ExcludedOn (model14.B 0 ++ [step14.q]) 9000000000000 (model14.caps 0)
    (model14.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6405000000000], [15000000000]) (some (10, 1, 4))
      (some (10, 1, 5)) (.next ([6285000000000], [135000000000]) (some (10, 1, 5)) (some (10, 1, 5))
      (.next ([6225000000000], [420000000000]) (some (10, 1, 5)) (some (10, 1, 5)) (.next
      ([5655000000000], [390000000000]) (some (10, 1, 5)) (some (10, 1, 5)) (.next ([5235000000000],
      [390000000000]) (some (10, 1, 5)) (some (10, 1, 5)) (.next ([5865000000000], [555000000000])
      (some (10, 1, 5)) (some (10, 1, 6)) (.next ([1739400000000, 2190000000000], [194400000000,
      2190000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next ([5475000000000], [795000000000])
      (some (10, 1, 6)) (some (10, 1, 6)) (.next ([5055000000000], [795000000000]) (some (10, 1, 6))
      (some (10, 1, 6)) fan14Owner0Part2)))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded14_1 : ExcludedOn (model14.B 1 ++ [step14.q]) 9000000000000 (model14.caps 1)
    (model14.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_2 : ExcludedOn (model14.B 2 ++ [step14.q]) 9000000000000 (model14.caps 2)
    (model14.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_4 : ExcludedOn (model14.B 4 ++ [step14.q]) 9000000000000 (model14.caps 4)
    (model14.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_5 : ExcludedOn (model14.B 5 ++ [step14.q]) 9000000000000 (model14.caps 5)
    (model14.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded14_4
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6405000000000], [15000000000]) (some (7, 10, 4))
      (some (7, 10, 5)) (.next ([6285000000000], [135000000000]) (some (7, 10, 5)) (some (7, 10, 5))
      (.next ([6225000000000], [420000000000]) (some (7, 10, 5)) (some (7, 10, 5)) (.next
      ([5655000000000], [390000000000]) (some (7, 10, 5)) (some (7, 10, 5)) (.next ([5235000000000],
      [390000000000]) (some (7, 10, 5)) (some (7, 10, 5)) fan15Owner0Part2)))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_4 : ExcludedOn (model15.B 4 ++ [step15.q]) 9000000000000 (model15.caps 4)
    (model15.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4413000000000], [375000000000]) (some (3, 0, 6))
      (some (3, 1, 6)) (.next ([120000000000], [30000000000]) (some (3, 1, 6)) (some (3, 1, 6))
      (.next ([2775000000000], [888000000000]) (some (3, 1, 6)) (some (4, 1, 6)) (.next
      ([2745000000000], [1038000000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next ([3900000000000,
      0], [1590000000000, 9000000000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next ([5655000000000],
      [2595000000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next ([5625000000000], [2745000000000])
      (some (4, 1, 6)) (some (4, 1, 6)) (.next ([2880000000000], [1707000000000]) (some (4, 1, 6))
      (some (4, 1, 6)) (.next ([4845000000000, 9000000000000], [4155000000000, -9000000000000])
      (some (4, 1, 6)) (some (4, 1, 6)) (.next ([2340000000000, 9000000000000], [2340000000000,
      9000000000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next ([630000000000], [780000000000,
      -9000000000000]) (some (4, 1, 6)) (some (4, 1, 6)) fan15Owner4Part0)))))))))))) (den :=
      9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded15_6 : ExcludedOn (model15.B 6 ++ [step15.q]) 9000000000000 (model15.caps 6)
    (model15.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6495000000000, 0], [165000000000,
      -9000000000000]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([6495000000000], [2505000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2340000000000, 9000000000000], [2340000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([4155000000000, -9000000000000],
      [4845000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [2340000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-165000000000,
      9000000000000], [6660000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next
      ([-2505000000000], [9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2340000000000,
      -9000000000000], [4680000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-4845000000000, -9000000000000], [9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.terminal (some (3, 1, 2)) (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded15_4
    · exact (hj rfl).elim
    · exact excluded15_6
    · exact excluded15_7
    · exact excluded15_8
    · exact excluded15_9
theorem next15 : model15.insert step15 = model16 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint260000270000
end ConwaySoifer.Simplified.Certificates
