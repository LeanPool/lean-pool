/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext260000270000
import Mathlib.Tactic.FinCases

/-!
# Sext 260000 270000 1

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
namespace Sext260000270000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan13Owner0Part0 : FanWitness := (.next ([-1950000000000], [6405000000000]) (some (11, 4, 7))
    (some (11, 4, 7)) (.next ([-750000000000], [2340000000000]) (some (11, 4, 7)) (some (11, 4, 7))
    (.next ([-1170000000000], [3300000000000]) (some (11, 4, 7)) (some (11, 4, 7)) (.next
    ([-795000000000], [2130000000000]) (some (11, 4, 7)) (some (11, 4, 7)) (.next ([-135000000000],
    [360000000000]) (some (11, 4, 7)) (some (11, 4, 7)) (.next ([-1170000000000], [2880000000000])
    (some (11, 4, 7)) (some (11, 4, 7)) (.next ([-375000000000], [750000000000]) (some (11, 4, 7))
    (some (11, 4, 11)) (.next ([-225000000000], [405000000000]) (some (11, 4, 11)) (some (11, 4,
    11)) (.next ([-1710000000000], [2880000000000]) (some (11, 4, 11)) (some (11, 5, 11)) (.next
    ([-1335000000000], [2130000000000]) (some (1, 5, 11)) (some (1, 5, 11)) (.next
    ([-2130000000000], [3300000000000]) (some (1, 5, 11)) (some (1, 5, 11)) (.next ([-795000000000],
    [1170000000000]) (some (1, 5, 11)) (some (1, 5, 11)) (.next ([-1335000000000], [1710000000000])
    (some (1, 5, 11)) (some (1, 5, 11)) (.next ([-1545000000000], [1965000000000]) (some (1, 5, 11))
    (some (1, 5, 11)) (.next ([-4695000000000], [5625000000000]) (some (1, 5, 11)) (some (1, 5, 11))
    (.next ([-5115000000000], [6045000000000]) (some (1, 5, 11)) (some (1, 5, 11)) (.next
    ([-5055000000000], [5850000000000]) (some (1, 5, 11)) (some (1, 5, 11)) (.next
    ([-5475000000000], [6270000000000]) (some (1, 5, 11)) (some (1, 5, 11)) (.next
    ([-5865000000000], [6420000000000]) (some (1, 5, 11)) (some (1, 5, 11)) (.next
    ([-5235000000000], [5625000000000]) (some (1, 5, 11)) (some (1, 5, 11)) (.next
    ([-5655000000000], [6045000000000]) (some (1, 5, 11)) (some (1, 5, 11)) (.next
    ([-6225000000000], [6645000000000]) (some (1, 5, 11)) (some (1, 5, 11)) (.next
    ([-6285000000000], [6420000000000]) (some (1, 5, 11)) (some (1, 5, 11)) (.next
    ([-6405000000000], [6420000000000]) (some (1, 5, 11)) (some (1, 5, 11)) (.terminal (some (1, 5,
    11)) (some (1, 5, 11)) (some (1, 5, 11)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan13Owner0Part1 : FanWitness := (.next ([555000000000], [5865000000000]) (some (11, 4, 5))
    (some (11, 4, 5)) (.next ([390000000000], [5235000000000]) (some (11, 4, 5)) (some (11, 4, 5))
    (.next ([390000000000], [5655000000000]) (some (11, 4, 5)) (some (11, 4, 6)) (.next
    ([420000000000], [6225000000000]) (some (11, 4, 6)) (some (11, 4, 6)) (.next ([135000000000],
    [6285000000000]) (some (11, 4, 6)) (some (11, 4, 6)) (.next ([15000000000], [6405000000000])
    (some (11, 4, 6)) (some (11, 4, 6)) (.next ([0], [1965000000000]) (some (11, 4, 6)) (some (11,
    4, 6)) (.next ([-240000000000], [7995000000000]) (some (11, 4, 6)) (some (11, 4, 7)) (.next
    ([-375000000000], [8355000000000]) (some (11, 4, 7)) (some (11, 4, 7)) (.next ([-405000000000],
    [6825000000000]) (some (11, 4, 7)) (some (11, 4, 7)) (.next ([-780000000000], [8535000000000])
    (some (11, 4, 7)) (some (11, 4, 7)) (.next ([-615000000000], [6660000000000]) (some (11, 4, 7))
    (some (11, 4, 7)) (.next ([-750000000000], [7020000000000]) (some (11, 4, 7)) (some (11, 4, 7))
    (.next ([-1035000000000], [6660000000000]) (some (11, 4, 7)) (some (11, 4, 7)) (.next
    ([-1155000000000], [7200000000000]) (some (11, 4, 7)) (some (11, 4, 7)) (.next
    ([-1170000000000], [7020000000000]) (some (11, 4, 7)) (some (11, 4, 7)) (.next ([-420000000000],
    [1965000000000]) (some (11, 4, 7)) (some (11, 4, 7)) (.next ([-1575000000000], [7200000000000])
    (some (11, 4, 7)) (some (11, 4, 7)) (.next ([-375000000000], [1710000000000]) (some (11, 4, 7))
    (some (11, 4, 7)) (.next ([-1410000000000], [6285000000000]) (some (11, 4, 7)) (some (11, 4, 7))
    (.next ([-1545000000000], [6645000000000]) (some (11, 4, 7)) (some (11, 4, 7)) (.next
    ([-1410000000000], [5865000000000]) (some (11, 4, 7)) (some (11, 4, 7)) (.next
    ([-1545000000000], [6225000000000]) (some (11, 4, 7)) (some (11, 4, 7)) (.next
    ([-1950000000000], [6825000000000]) (some (11, 4, 7)) (some (11, 4, 7))
    fan13Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan13Owner0Part2 : FanWitness := (.next ([1335000000000], [375000000000]) (some (11, 2, 5))
    (some (11, 2, 5)) (.next ([4875000000000], [1410000000000]) (some (11, 2, 5)) (some (11, 2, 5))
    (.next ([5100000000000], [1545000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next
    ([4455000000000], [1410000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next ([4680000000000],
    [1545000000000]) (some (11, 2, 5)) (some (11, 3, 5)) (.next ([4875000000000], [1950000000000])
    (some (11, 3, 5)) (some (11, 3, 5)) (.next ([4455000000000], [1950000000000]) (some (11, 3, 5))
    (some (11, 3, 5)) (.next ([1590000000000], [750000000000]) (some (11, 3, 5)) (some (11, 3, 5))
    (.next ([2130000000000], [1170000000000]) (some (11, 3, 5)) (some (11, 3, 5)) (.next
    ([1335000000000], [795000000000]) (some (11, 3, 5)) (some (11, 3, 5)) (.next ([225000000000],
    [135000000000]) (some (11, 3, 5)) (some (11, 3, 5)) (.next ([1710000000000], [1170000000000])
    (some (11, 3, 5)) (some (11, 4, 5)) (.next ([375000000000], [375000000000]) (some (11, 4, 5))
    (some (11, 4, 5)) (.next ([180000000000], [225000000000]) (some (11, 4, 5)) (some (11, 4, 5))
    (.next ([1170000000000], [1710000000000]) (some (11, 4, 5)) (some (11, 4, 5)) (.next
    ([795000000000], [1335000000000]) (some (11, 4, 5)) (some (11, 4, 5)) (.next ([1170000000000],
    [2130000000000]) (some (11, 4, 5)) (some (11, 4, 5)) (.next ([375000000000], [795000000000])
    (some (11, 4, 5)) (some (11, 4, 5)) (.next ([375000000000], [1335000000000]) (some (11, 4, 5))
    (some (11, 4, 5)) (.next ([420000000000], [1545000000000]) (some (11, 4, 5)) (some (11, 4, 5))
    (.next ([930000000000], [4695000000000]) (some (11, 4, 5)) (some (11, 4, 5)) (.next
    ([930000000000], [5115000000000]) (some (11, 4, 5)) (some (11, 4, 5)) (.next ([795000000000],
    [5055000000000]) (some (11, 4, 5)) (some (11, 4, 5)) (.next ([795000000000], [5475000000000])
    (some (11, 4, 5)) (some (11, 4, 5)) fan13Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner0Part0 : FanWitness := (.next ([-4413000000000], [9420000000000]) (some (0, 11, 7))
    (some (0, 11, 7)) (.next ([-375000000000], [750000000000]) (some (0, 11, 7)) (some (0, 11, 7))
    (.next ([-5163000000000], [9795000000000]) (some (0, 11, 7)) (some (1, 11, 8)) (.next
    ([-225000000000], [405000000000]) (some (1, 11, 8)) (some (1, 11, 8)) (.next ([-5583000000000],
    [9795000000000]) (some (1, 11, 8)) (some (1, 11, 8)) (.next ([-5958000000000], [9420000000000])
    (some (1, 11, 8)) (some (1, 11, 8)) (.next ([-5163000000000], [7830000000000]) (some (1, 11, 8))
    (some (1, 11, 8)) (.next ([-5958000000000], [9000000000000]) (some (1, 11, 8)) (some (1, 11, 8))
    (.next ([-5583000000000], [8250000000000]) (some (1, 11, 8)) (some (1, 11, 8)) (.next
    ([-795000000000], [1170000000000]) (some (1, 11, 8)) (some (11, 11, 8)) (.next
    ([-3375000000000], [4617000000000]) (some (11, 11, 8)) (some (11, 11, 8)) (.next
    ([-3150000000000], [4212000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next
    ([-1545000000000], [1965000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next
    ([-3375000000000], [4077000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next
    ([-4695000000000], [5625000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next
    ([-5115000000000], [6045000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next
    ([-5055000000000], [5850000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next
    ([-5475000000000], [6270000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next
    ([-5865000000000], [6420000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next
    ([-5235000000000], [5625000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next
    ([-5655000000000], [6045000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next
    ([-6225000000000], [6645000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next
    ([-6285000000000], [6420000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next
    ([-6405000000000], [6420000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.terminal (some (11, 5,
    8)) (some (11, 5, 8)) (some (11, 5, 8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner0Part1 : FanWitness := (.next ([555000000000], [5865000000000]) (some (10, 11, 5))
    (some (10, 11, 5)) (.next ([390000000000], [5235000000000]) (some (10, 11, 5)) (some (10, 11,
    5)) (.next ([390000000000], [5655000000000]) (some (10, 11, 5)) (some (10, 11, 6)) (.next
    ([420000000000], [6225000000000]) (some (10, 11, 6)) (some (10, 11, 6)) (.next ([135000000000],
    [6285000000000]) (some (10, 11, 6)) (some (10, 11, 6)) (.next ([15000000000], [6405000000000])
    (some (10, 11, 6)) (some (10, 11, 6)) (.next ([0], [1965000000000]) (some (10, 11, 6)) (some
    (10, 11, 6)) (.next ([-405000000000], [6825000000000]) (some (0, 11, 6)) (some (0, 11, 7))
    (.next ([-615000000000], [6660000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next
    ([-750000000000], [7020000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next ([-1035000000000],
    [6660000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next ([-1155000000000], [7200000000000])
    (some (0, 11, 7)) (some (0, 11, 7)) (.next ([-1170000000000], [7020000000000]) (some (0, 11, 7))
    (some (0, 11, 7)) (.next ([-420000000000], [1965000000000]) (some (0, 11, 7)) (some (0, 11, 7))
    (.next ([-1575000000000], [7200000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next
    ([-1410000000000], [6285000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next
    ([-1545000000000], [6645000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next
    ([-1410000000000], [5865000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next
    ([-1545000000000], [6225000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next
    ([-1950000000000], [6825000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next
    ([-1950000000000], [6405000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next ([-750000000000],
    [2340000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next ([-135000000000], [360000000000])
    (some (0, 11, 7)) (some (0, 11, 7)) (.next ([-3993000000000], [9000000000000]) (some (0, 11, 7))
    (some (0, 11, 7)) fan14Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner0Part2 : FanWitness := (.next ([4680000000000], [1545000000000]) (some (9, 11, 5))
    (some (9, 11, 5)) (.next ([4875000000000], [1950000000000]) (some (9, 11, 5)) (some (9, 11, 5))
    (.next ([4455000000000], [1950000000000]) (some (9, 11, 5)) (some (9, 11, 5)) (.next
    ([1590000000000], [750000000000]) (some (9, 11, 5)) (some (9, 11, 5)) (.next ([225000000000],
    [135000000000]) (some (9, 11, 5)) (some (9, 11, 5)) (.next ([5007000000000], [3993000000000])
    (some (9, 11, 5)) (some (9, 11, 5)) (.next ([5007000000000], [4413000000000]) (some (9, 11, 5))
    (some (9, 11, 5)) (.next ([375000000000], [375000000000]) (some (9, 11, 5)) (some (9, 11, 5))
    (.next ([4632000000000], [5163000000000]) (some (9, 11, 5)) (some (10, 11, 5)) (.next
    ([180000000000], [225000000000]) (some (10, 11, 5)) (some (10, 11, 5)) (.next ([4212000000000],
    [5583000000000]) (some (10, 11, 5)) (some (10, 11, 5)) (.next ([3462000000000], [5958000000000])
    (some (10, 11, 5)) (some (10, 11, 5)) (.next ([2667000000000], [5163000000000]) (some (10, 11,
    5)) (some (10, 11, 5)) (.next ([3042000000000], [5958000000000]) (some (10, 11, 5)) (some (10,
    11, 5)) (.next ([2667000000000], [5583000000000]) (some (10, 11, 5)) (some (10, 11, 5)) (.next
    ([375000000000], [795000000000]) (some (10, 11, 5)) (some (10, 11, 5)) (.next ([1242000000000],
    [3375000000000]) (some (10, 11, 5)) (some (10, 11, 5)) (.next ([1062000000000], [3150000000000])
    (some (10, 11, 5)) (some (10, 11, 5)) (.next ([420000000000], [1545000000000]) (some (10, 11,
    5)) (some (10, 11, 5)) (.next ([702000000000], [3375000000000]) (some (10, 11, 5)) (some (10,
    11, 5)) (.next ([930000000000], [4695000000000]) (some (10, 11, 5)) (some (10, 11, 5)) (.next
    ([930000000000], [5115000000000]) (some (10, 11, 5)) (some (10, 11, 5)) (.next ([795000000000],
    [5055000000000]) (some (10, 11, 5)) (some (10, 11, 5)) (.next ([795000000000], [5475000000000])
    (some (10, 11, 5)) (some (10, 11, 5)) fan14Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner0Part0 : FanWitness := (.next ([-375000000000], [750000000000]) (some (0, 11, 7))
    (some (0, 11, 7)) (.next ([-4935000000000], [9795000000000]) (some (0, 11, 7)) (some (1, 11, 8))
    (.next ([-225000000000], [405000000000]) (some (1, 11, 8)) (some (1, 11, 8)) (.next
    ([-5685000000000], [10170000000000]) (some (1, 11, 8)) (some (1, 11, 8)) (.next
    ([-6105000000000], [10170000000000]) (some (1, 11, 8)) (some (1, 11, 8)) (.next
    ([-6480000000000], [9795000000000]) (some (1, 11, 8)) (some (1, 11, 8)) (.next ([-795000000000],
    [1170000000000]) (some (1, 11, 8)) (some (1, 11, 8)) (.next ([-6480000000000], [9375000000000])
    (some (1, 11, 8)) (some (1, 11, 8)) (.next ([-5685000000000], [8205000000000]) (some (1, 11, 8))
    (some (1, 11, 8)) (.next ([-6105000000000], [8625000000000]) (some (1, 11, 8)) (some (1, 11, 8))
    (.next ([-1545000000000], [1965000000000]) (some (1, 11, 8)) (some (11, 11, 8)) (.next
    ([-4695000000000], [5625000000000]) (some (11, 11, 8)) (some (11, 11, 8)) (.next
    ([-3750000000000], [4470000000000]) (some (11, 11, 8)) (some (11, 11, 8)) (.next
    ([-5115000000000], [6045000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next
    ([-5055000000000], [5850000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next
    ([-3525000000000], [4065000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next
    ([-5475000000000], [6270000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next
    ([-5865000000000], [6420000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next
    ([-5235000000000], [5625000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next
    ([-5655000000000], [6045000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next
    ([-6225000000000], [6645000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next
    ([-3750000000000], [3930000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next
    ([-6285000000000], [6420000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next
    ([-6405000000000], [6420000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.terminal (some (11, 5,
    8)) (some (11, 5, 8)) (some (11, 5, 8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner0Part1 : FanWitness := (.next ([390000000000], [5235000000000]) (some (10, 11, 5))
    (some (10, 11, 5)) (.next ([390000000000], [5655000000000]) (some (10, 11, 5)) (some (10, 11,
    6)) (.next ([420000000000], [6225000000000]) (some (10, 11, 6)) (some (10, 11, 6)) (.next
    ([180000000000], [3750000000000]) (some (10, 11, 6)) (some (10, 11, 6)) (.next ([135000000000],
    [6285000000000]) (some (10, 11, 6)) (some (10, 11, 6)) (.next ([15000000000], [6405000000000])
    (some (10, 11, 6)) (some (10, 11, 6)) (.next ([0], [1965000000000]) (some (10, 11, 6)) (some
    (10, 11, 6)) (.next ([-405000000000], [6825000000000]) (some (0, 11, 6)) (some (0, 11, 7))
    (.next ([-615000000000], [6660000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next
    ([-750000000000], [7020000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next ([-1035000000000],
    [6660000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next ([-1155000000000], [7200000000000])
    (some (0, 11, 7)) (some (0, 11, 7)) (.next ([-1170000000000], [7020000000000]) (some (0, 11, 7))
    (some (0, 11, 7)) (.next ([-420000000000], [1965000000000]) (some (0, 11, 7)) (some (0, 11, 7))
    (.next ([-1575000000000], [7200000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next
    ([-1410000000000], [6285000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next
    ([-1545000000000], [6645000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next
    ([-1410000000000], [5865000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next
    ([-1545000000000], [6225000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next
    ([-1950000000000], [6825000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next
    ([-1950000000000], [6405000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next ([-750000000000],
    [2340000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next ([-135000000000], [360000000000])
    (some (0, 11, 7)) (some (0, 11, 7)) (.next ([-4515000000000], [9375000000000]) (some (0, 11, 7))
    (some (0, 11, 7)) fan15Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner0Part2 : FanWitness := (.next ([4680000000000], [1545000000000]) (some (9, 11, 5))
    (some (9, 11, 5)) (.next ([4875000000000], [1950000000000]) (some (9, 11, 5)) (some (9, 11, 5))
    (.next ([4455000000000], [1950000000000]) (some (9, 11, 5)) (some (9, 11, 5)) (.next
    ([1590000000000], [750000000000]) (some (9, 11, 5)) (some (9, 11, 5)) (.next ([225000000000],
    [135000000000]) (some (9, 11, 5)) (some (9, 11, 5)) (.next ([4860000000000], [4515000000000])
    (some (9, 11, 5)) (some (9, 11, 5)) (.next ([375000000000], [375000000000]) (some (9, 11, 5))
    (some (9, 11, 5)) (.next ([4860000000000], [4935000000000]) (some (9, 11, 5)) (some (10, 11, 5))
    (.next ([180000000000], [225000000000]) (some (10, 11, 5)) (some (10, 11, 5)) (.next
    ([4485000000000], [5685000000000]) (some (10, 11, 5)) (some (10, 11, 5)) (.next
    ([4065000000000], [6105000000000]) (some (10, 11, 5)) (some (10, 11, 5)) (.next
    ([3315000000000], [6480000000000]) (some (10, 11, 5)) (some (10, 11, 5)) (.next ([375000000000],
    [795000000000]) (some (10, 11, 5)) (some (10, 11, 5)) (.next ([2895000000000], [6480000000000])
    (some (10, 11, 5)) (some (10, 11, 5)) (.next ([2520000000000], [5685000000000]) (some (10, 11,
    5)) (some (10, 11, 5)) (.next ([2520000000000], [6105000000000]) (some (10, 11, 5)) (some (10,
    11, 5)) (.next ([420000000000], [1545000000000]) (some (10, 11, 5)) (some (10, 11, 5)) (.next
    ([930000000000], [4695000000000]) (some (10, 11, 5)) (some (10, 11, 5)) (.next ([720000000000],
    [3750000000000]) (some (10, 11, 5)) (some (10, 11, 5)) (.next ([930000000000], [5115000000000])
    (some (10, 11, 5)) (some (10, 11, 5)) (.next ([795000000000], [5055000000000]) (some (10, 11,
    5)) (some (10, 11, 5)) (.next ([540000000000], [3525000000000]) (some (10, 11, 5)) (some (10,
    11, 5)) (.next ([795000000000], [5475000000000]) (some (10, 11, 5)) (some (10, 11, 5)) (.next
    ([555000000000], [5865000000000]) (some (10, 11, 5)) (some (10, 11, 5))
    fan15Owner0Part1))))))))))))))))))))))))

theorem excluded8_1 : ExcludedOn (model8.B 1 ++ [step8.q]) 9000000000000 (model8.caps 1) (model8.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3510000000000], [2910000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([2340000000000, 9000000000000], [2340000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([3510000000000], [5250000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([1170000000000, -9000000000000], [7590000000000,
      9000000000000]) (some (0, 3, 2)) none (.next ([0, 0], [2340000000000, 9000000000000]) none
      none (.next ([-2910000000000, 9000000000000], [6420000000000, -9000000000000]) none none
      (.next ([-2340000000000, -9000000000000], [4680000000000, 18000000000000]) (some (3, 1, 0))
      (some (3, 1, 0)) (.next ([-5250000000000], [8760000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-7590000000000, -9000000000000], [8760000000000, 0]) (some (3, 1, 0)) (some (3, 1,
      0)) (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_2 : ExcludedOn (model8.B 2 ++ [step8.q]) 9000000000000 (model8.caps 2) (model8.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_3 : ExcludedOn (model8.B 3 ++ [step8.q]) 9000000000000 (model8.caps 3) (model8.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_4 : ExcludedOn (model8.B 4 ++ [step8.q]) 9000000000000 (model8.caps 4) (model8.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_5 : ExcludedOn (model8.B 5 ++ [step8.q]) 9000000000000 (model8.caps 5) (model8.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7830000000000, 9000000000000], [1410000000000,
      -9000000000000]) (some (3, 0, 3)) (some (3, 1, 3)) (.next ([5490000000000], [3750000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2340000000000, 9000000000000], [2340000000000,
      9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([3150000000000, -9000000000000],
      [3750000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0], [2340000000000,
      9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1410000000000, 9000000000000],
      [9240000000000, 0]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-3750000000000],
      [9240000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2340000000000, -9000000000000],
      [4680000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3750000000000,
      0], [6900000000000, -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 3, 3)) (some (0, 3, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_6 : ExcludedOn (model8.B 6 ++ [step8.q]) 9000000000000 (model8.caps 6) (model8.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2580000000000, 9000000000000], [1170000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([3510000000000], [2910000000000,
      -9000000000000]) (some (2, 0, 2)) (some (2, 0, 2)) (.next ([2340000000000, 9000000000000],
      [6660000000000, -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([240000000000],
      [3510000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [2340000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-1170000000000, 9000000000000],
      [3750000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-2910000000000, 9000000000000],
      [6420000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6660000000000,
      9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-3510000000000], [3750000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([3150000000000], [3135000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([2340000000000, 9000000000000], [2340000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([3150000000000], [5475000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([810000000000, -9000000000000], [7815000000000,
      9000000000000]) (some (0, 3, 2)) none (.next ([0, 0], [2340000000000, 9000000000000]) none
      none (.next ([-3135000000000, 9000000000000], [6285000000000, -9000000000000]) none none
      (.next ([-2340000000000, -9000000000000], [4680000000000, 18000000000000]) (some (3, 1, 0))
      (some (3, 1, 0)) (.next ([-5475000000000], [8625000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-7815000000000, -9000000000000], [8625000000000, 0]) (some (3, 1, 0)) (some (3, 1,
      0)) (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_2 : ExcludedOn (model9.B 2 ++ [step9.q]) 9000000000000 (model9.caps 2) (model9.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_3 : ExcludedOn (model9.B 3 ++ [step9.q]) 9000000000000 (model9.caps 3) (model9.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_4 : ExcludedOn (model9.B 4 ++ [step9.q]) 9000000000000 (model9.caps 4) (model9.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_5 : ExcludedOn (model9.B 5 ++ [step9.q]) 9000000000000 (model9.caps 5) (model9.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8190000000000, 9000000000000], [1185000000000,
      -9000000000000]) (some (3, 0, 3)) (some (3, 1, 3)) (.next ([5850000000000], [3525000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2340000000000, 9000000000000], [2340000000000,
      9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([3510000000000, -9000000000000],
      [3525000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0], [2340000000000,
      9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1185000000000, 9000000000000],
      [9375000000000, 0]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-3525000000000],
      [9375000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2340000000000, -9000000000000],
      [4680000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3525000000000,
      0], [7035000000000, -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 3, 3)) (some (0, 3, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_6 : ExcludedOn (model9.B 6 ++ [step9.q]) 9000000000000 (model9.caps 6) (model9.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2715000000000, 9000000000000], [810000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([3150000000000], [3135000000000,
      -9000000000000]) (some (2, 0, 2)) (some (2, 0, 2)) (.next ([2340000000000, 9000000000000],
      [6660000000000, -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([375000000000],
      [3150000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [2340000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-810000000000, 9000000000000],
      [3525000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-3135000000000, 9000000000000],
      [6285000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6660000000000,
      9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-3150000000000], [3525000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
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

theorem excluded10_1 : ExcludedOn (model10.B 1 ++ [step10.q]) 9000000000000 (model10.caps 1)
    (model10.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2970000000000], [2910000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([2340000000000, 9000000000000], [2340000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([2970000000000], [5250000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([630000000000, -9000000000000], [7590000000000,
      9000000000000]) (some (0, 3, 2)) none (.next ([0, 0], [2340000000000, 9000000000000]) none
      none (.next ([-2910000000000, 9000000000000], [5880000000000, -9000000000000]) none none
      (.next ([-2340000000000, -9000000000000], [4680000000000, 18000000000000]) (some (3, 1, 0))
      (some (3, 1, 0)) (.next ([-5250000000000], [8220000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-7590000000000, -9000000000000], [8220000000000, 0]) (some (3, 1, 0)) (some (3, 1,
      0)) (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded10_2 : ExcludedOn (model10.B 2 ++ [step10.q]) 9000000000000 (model10.caps 2)
    (model10.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_3 : ExcludedOn (model10.B 3 ++ [step10.q]) 9000000000000 (model10.caps 3)
    (model10.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_4 : ExcludedOn (model10.B 4 ++ [step10.q]) 9000000000000 (model10.caps 4)
    (model10.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_5 : ExcludedOn (model10.B 5 ++ [step10.q]) 9000000000000 (model10.caps 5)
    (model10.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_6 : ExcludedOn (model10.B 6 ++ [step10.q]) 9000000000000 (model10.caps 6)
    (model10.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3120000000000, 9000000000000], [630000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([2970000000000], [2910000000000,
      -9000000000000]) (some (2, 0, 2)) (some (2, 0, 2)) (.next ([2340000000000, 9000000000000],
      [6660000000000, -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([780000000000],
      [2970000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [2340000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-630000000000, 9000000000000],
      [3750000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-2910000000000, 9000000000000],
      [5880000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6660000000000,
      9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2970000000000], [3750000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded10_7 : ExcludedOn (model10.B 7 ++ [step10.q]) 9000000000000 (model10.caps 7)
    (model10.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_8 : ExcludedOn (model10.B 8 ++ [step10.q]) 9000000000000 (model10.caps 8)
    (model10.ord 8) 0 1 100 := by
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
    · exact (hj rfl).elim
    · exact excluded10_1
    · exact excluded10_2
    · exact excluded10_3
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
  apply ExclusionHint.sound (.pair 0 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_4 : ExcludedOn (model11.B 4 ++ [step11.q]) 9000000000000 (model11.caps 4)
    (model11.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_5 : ExcludedOn (model11.B 5 ++ [step11.q]) 9000000000000 (model11.caps 5)
    (model11.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_6 : ExcludedOn (model11.B 6 ++ [step11.q]) 9000000000000 (model11.caps 6)
    (model11.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1560000000000, 0], [30000000000, 9000000000000])
      (some (2, 0, 1)) (some (2, 0, 2)) (.next ([750000000000], [1560000000000]) (some (2, 0, 2))
      (some (2, 3, 2)) (.next ([2340000000000, 9000000000000], [6660000000000, -9000000000000])
      (some (2, 3, 2)) (some (2, 3, 2)) (.next ([750000000000], [8220000000000, -9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [2340000000000, 9000000000000]) (some (0, 3,
      2)) (some (0, 3, 2)) (.next ([-30000000000, -9000000000000], [1590000000000, 9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-1560000000000], [2310000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-6660000000000, 9000000000000], [9000000000000, 0]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-8220000000000, 9000000000000], [8970000000000, -9000000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1, 2)) (some (0, 1,
      2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
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
    · exact excluded11_5
    · exact excluded11_6
    · exact excluded11_7
    · exact excluded11_8
    · exact (hj rfl).elim
theorem next11 : model11.insert step11 = model12 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded12_0 : ExcludedOn (model12.B 0 ++ [step12.q]) 9000000000000 (model12.caps 0)
    (model12.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_4 : ExcludedOn (model12.B 4 ++ [step12.q]) 9000000000000 (model12.caps 4)
    (model12.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_5 : ExcludedOn (model12.B 5 ++ [step12.q]) 9000000000000 (model12.caps 5)
    (model12.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_6 : ExcludedOn (model12.B 6 ++ [step12.q]) 9000000000000 (model12.caps 6)
    (model12.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1560000000000, 0], [780000000000,
      9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([2340000000000, 9000000000000],
      [6660000000000, -9000000000000]) (some (2, 0, 2)) (some (2, 3, 2)) (.next ([0, 0],
      [2340000000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-780000000000,
      -9000000000000], [2340000000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next
      ([-6660000000000, 9000000000000], [9000000000000, 0]) (some (0, 3, 2)) (some (0, 3, 2))
      (.terminal (some (0, 3, 2)) (some (0, 1, 2)) (some (0, 3, 2))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded12_5
    · exact excluded12_6
    · exact excluded12_7
    · exact excluded12_8
    · exact (hj rfl).elim
theorem next12 : model12.insert step12 = model13 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded13_0 : ExcludedOn (model13.B 0 ++ [step13.q]) 9000000000000 (model13.caps 0)
    (model13.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7755000000000], [240000000000]) (some (11, 1,
      5)) (some (11, 2, 5)) (.next ([7980000000000], [375000000000]) (some (11, 2, 5)) (some (11, 2,
      5)) (.next ([6420000000000], [405000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next
      ([7755000000000], [780000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next ([6045000000000],
      [615000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next ([6270000000000], [750000000000])
      (some (11, 2, 5)) (some (11, 2, 5)) (.next ([5625000000000], [1035000000000]) (some (11, 2,
      5)) (some (11, 2, 5)) (.next ([6045000000000], [1155000000000]) (some (11, 2, 5)) (some (11,
      2, 5)) (.next ([5850000000000], [1170000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next
      ([1545000000000], [420000000000]) (some (11, 2, 5)) (some (11, 2, 5)) (.next ([5625000000000],
      [1575000000000]) (some (11, 2, 5)) (some (11, 2, 5)) fan13Owner0Part2)))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_1 : ExcludedOn (model13.B 1 ++ [step13.q]) 9000000000000 (model13.caps 1)
    (model13.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_2 : ExcludedOn (model13.B 2 ++ [step13.q]) 9000000000000 (model13.caps 2)
    (model13.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4845000000000, 9000000000000], [4155000000000,
      -9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2340000000000, 9000000000000],
      [2340000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2505000000000],
      [6495000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([165000000000, -9000000000000],
      [6495000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0, 0], [2340000000000,
      9000000000000]) (some (0, 3, 1)) (some (3, 3, 1)) (.next ([-4155000000000, 9000000000000],
      [9000000000000, 0]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([-2340000000000,
      -9000000000000], [4680000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-6495000000000], [9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-6495000000000,
      0], [6660000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_4 : ExcludedOn (model13.B 4 ++ [step13.q]) 9000000000000 (model13.caps 4)
    (model13.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6495000000000], [165000000000, -9000000000000])
      (some (3, 0, 3)) (some (3, 1, 3)) (.next ([6495000000000], [2505000000000]) (some (2, 1, 3))
      (some (2, 1, 3)) (.next ([2340000000000, 9000000000000], [2340000000000, 9000000000000]) (some
      (2, 1, 3)) (some (2, 1, 3)) (.next ([4155000000000, -9000000000000], [4845000000000,
      9000000000000]) (some (2, 1, 3)) (some (2, 1, 3)) (.next ([0, 0], [2340000000000,
      9000000000000]) (some (2, 1, 3)) (some (2, 1, 3)) (.next ([-165000000000, 9000000000000],
      [6660000000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2505000000000],
      [9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2340000000000, -9000000000000],
      [4680000000000, 18000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-4845000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1,
      3)) (some (0, 3, 3)) (some (0, 3, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_5 : ExcludedOn (model13.B 5 ++ [step13.q]) 9000000000000 (model13.caps 5)
    (model13.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded13_4
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6420000000000], [405000000000]) (some (8, 11,
      5)) (some (9, 11, 5)) (.next ([6045000000000], [615000000000]) (some (9, 11, 5)) (some (9, 11,
      5)) (.next ([6270000000000], [750000000000]) (some (9, 11, 5)) (some (9, 11, 5)) (.next
      ([5625000000000], [1035000000000]) (some (9, 11, 5)) (some (9, 11, 5)) (.next
      ([6045000000000], [1155000000000]) (some (9, 11, 5)) (some (9, 11, 5)) (.next
      ([5850000000000], [1170000000000]) (some (9, 11, 5)) (some (9, 11, 5)) (.next
      ([1545000000000], [420000000000]) (some (9, 11, 5)) (some (9, 11, 5)) (.next ([5625000000000],
      [1575000000000]) (some (9, 11, 5)) (some (9, 11, 5)) (.next ([4875000000000], [1410000000000])
      (some (9, 11, 5)) (some (9, 11, 5)) (.next ([5100000000000], [1545000000000]) (some (9, 11,
      5)) (some (9, 11, 5)) (.next ([4455000000000], [1410000000000]) (some (9, 11, 5)) (some (9,
      11, 5)) fan14Owner0Part2)))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_4 : ExcludedOn (model14.B 4 ++ [step14.q]) 9000000000000 (model14.caps 4)
    (model14.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_6 : ExcludedOn (model14.B 6 ++ [step14.q]) 9000000000000 (model14.caps 6)
    (model14.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6690000000000], [750000000000]) (some (4, 0, 1))
      (some (4, 1, 2)) (.next ([5163000000000, 0], [1872000000000, -9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([1935000000000], [1527000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([5163000000000], [4212000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([1935000000000], [2277000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2340000000000,
      9000000000000], [5100000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([1590000000000, 9000000000000], [5100000000000, -9000000000000]) (some (4, 1, 2)) (some (4,
      1, 2)) (.next ([0, 0], [2340000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([-750000000000], [7440000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-1872000000000, 9000000000000], [7035000000000, -9000000000000]) (some (4, 1, 2)) (some (4,
      1, 2)) (.next ([-1527000000000], [3462000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-4212000000000], [9375000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2277000000000], [4212000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5100000000000,
      9000000000000], [7440000000000, 0]) (some (0, 1, 2)) (some (0, 1, 4)) (.next ([-5100000000000,
      9000000000000], [6690000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.terminal (some (0, 1,
      4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded14_4
    · exact (hj rfl).elim
    · exact excluded14_6
    · exact excluded14_7
    · exact excluded14_8
    · exact excluded14_9
theorem next14 : model14.insert step14 = model15 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded15_0 : ExcludedOn (model15.B 0 ++ [step15.q]) 9000000000000 (model15.caps 0)
    (model15.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6420000000000], [405000000000]) (some (8, 11,
      5)) (some (9, 11, 5)) (.next ([6045000000000], [615000000000]) (some (9, 11, 5)) (some (9, 11,
      5)) (.next ([6270000000000], [750000000000]) (some (9, 11, 5)) (some (9, 11, 5)) (.next
      ([5625000000000], [1035000000000]) (some (9, 11, 5)) (some (9, 11, 5)) (.next
      ([6045000000000], [1155000000000]) (some (9, 11, 5)) (some (9, 11, 5)) (.next
      ([5850000000000], [1170000000000]) (some (9, 11, 5)) (some (9, 11, 5)) (.next
      ([1545000000000], [420000000000]) (some (9, 11, 5)) (some (9, 11, 5)) (.next ([5625000000000],
      [1575000000000]) (some (9, 11, 5)) (some (9, 11, 5)) (.next ([4875000000000], [1410000000000])
      (some (9, 11, 5)) (some (9, 11, 5)) (.next ([5100000000000], [1545000000000]) (some (9, 11,
      5)) (some (9, 11, 5)) (.next ([4455000000000], [1410000000000]) (some (9, 11, 5)) (some (9,
      11, 5)) fan15Owner0Part2)))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_4 : ExcludedOn (model15.B 4 ++ [step15.q]) 9000000000000 (model15.caps 4)
    (model15.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_6 : ExcludedOn (model15.B 6 ++ [step15.q]) 9000000000000 (model15.caps 6)
    (model15.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6690000000000], [750000000000]) (some (4, 0, 1))
      (some (4, 1, 2)) (.next ([5310000000000, 0], [1350000000000, -9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([5310000000000], [3690000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([1560000000000], [1380000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([1560000000000], [2130000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2340000000000,
      9000000000000], [5100000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([1590000000000, 9000000000000], [5100000000000, -9000000000000]) (some (4, 1, 2)) (some (4,
      1, 2)) (.next ([0, 0], [2340000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([-750000000000], [7440000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-1350000000000, 9000000000000], [6660000000000, -9000000000000]) (some (4, 1, 2)) (some (4,
      1, 2)) (.next ([-3690000000000], [9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-1380000000000], [2940000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2130000000000], [3690000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5100000000000,
      9000000000000], [7440000000000, 0]) (some (0, 1, 2)) (some (0, 1, 4)) (.next ([-5100000000000,
      9000000000000], [6690000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.terminal (some (0, 1,
      4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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

end Sext260000270000
end ConwaySoifer.Simplified.Certificates
