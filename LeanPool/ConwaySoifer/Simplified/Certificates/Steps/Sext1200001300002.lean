/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext120000130000
import Mathlib.Tactic.FinCases

/-!
# Sext 120000 130000 2

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
namespace Sext120000130000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan16Owner4Part0 : FanWitness := (.next ([3105000000000], [1770000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([5040000000000], [4755000000000]) (some (5, 1, 2)) (some (5, 1, 3))
    (.next ([4905000000000], [4680000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([1830000000000, 9000000000000], [2160000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1,
    3)) (.next ([1800000000000], [2910000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([1080000000000], [2880000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 5)) (.next
    ([1080000000000], [3960000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([750000000000],
    [3240000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1080000000000, 9000000000000],
    [5835000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([945000000000, 9000000000000],
    [5760000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0], [5835000000000]) (some (4, 1,
    5)) (some (4, 1, 5)) (.next ([-135000000000], [5760000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-75000000000], [210000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-1845000000000], [5085000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1770000000000],
    [4875000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4755000000000], [9795000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4680000000000], [9585000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-2160000000000, 9000000000000], [3990000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-2910000000000], [4710000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-2880000000000, 9000000000000], [3960000000000, -9000000000000]) (some (0, 1, 5)) (some
    (0, 1, 5)) (.next ([-3960000000000], [5040000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-3240000000000], [3990000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5835000000000],
    [6915000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5760000000000],
    [6705000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.terminal (some (0, 1, 5))
    (some (0, 1, 5)) (some (0, 1, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner0Part0 : FanWitness := (.next ([226800000000, -2610000000000], [5711400000000,
    5220000000000]) (some (0, 7, 5)) (some (7, 7, 5)) (.next ([46800000000, -2610000000000],
    [5801400000000, 5220000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([0, 0], [939600000000,
    7830000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([-86400000000, -5220000000000],
    [5398200000000, 2610000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([-266400000000,
    -5220000000000], [5488200000000, 2610000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next
    ([-45000000000], [720000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([-1875000000000],
    [8040000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([-1965000000000], [8220000000000])
    (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-1920000000000], [7500000000000]) (some (7, 3, 5))
    (some (7, 3, 5)) (.next ([-313200000000, -2610000000000], [626400000000, 5220000000000]) (some
    (7, 3, 5)) (some (7, 3, 5)) (.next ([-4186800000000, 2610000000000], [5893200000000,
    2610000000000]) (some (7, 3, 5)) (some (7, 4, 6)) (.next ([-4813200000000, -2610000000000],
    [6206400000000, 5220000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-4771800000000,
    2610000000000], [5938200000000, 2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-4861800000000, 2610000000000], [5848200000000, 2610000000000]) (some (7, 4, 6)) (some (7, 4,
    6)) (.next ([-7813200000000, -2610000000000], [9206400000000, 5220000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-5398200000000, -2610000000000], [6251400000000, 5220000000000]) (some
    (7, 4, 6)) (some (7, 4, 6)) (.next ([-5126400000000, -5220000000000], [5893200000000,
    2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5488200000000, -2610000000000],
    [6161400000000, 5220000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-7186800000000,
    2610000000000], [7953600000000, -5220000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-8126400000000, -5220000000000], [8893200000000, 2610000000000]) (some (7, 4, 6)) (some (7, 4,
    6)) (.next ([-4813200000000, -2610000000000], [5266800000000, -2610000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-7813200000000, -2610000000000], [8266800000000, -2610000000000])
    (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5711400000000, -5220000000000], [5938200000000,
    2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5801400000000, -5220000000000],
    [5848200000000, 2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.terminal (some (7, 4, 6))
    (some (7, 4, 6)) (some (7, 4, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner4Part0 : FanWitness := (.next ([1665000000000], [420000000000]) (some (4, 1, 5)) (some
    (4, 1, 5)) (.next ([135000000000], [75000000000]) (some (4, 1, 5)) (some (4, 5, 5)) (.next
    ([3240000000000], [1845000000000]) (some (4, 5, 5)) (some (4, 5, 5)) (.next ([3105000000000],
    [1770000000000]) (some (4, 5, 5)) (some (4, 5, 5)) (.next ([1830000000000, 9000000000000],
    [2160000000000, -9000000000000]) (some (4, 5, 5)) (some (4, 5, 5)) (.next ([2820000000000],
    [3930000000000]) (some (4, 5, 5)) (some (4, 5, 5)) (.next ([750000000000], [3240000000000])
    (some (4, 5, 3)) (some (4, 5, 3)) (.next ([1080000000000, 9000000000000], [5835000000000]) (some
    (4, 5, 3)) (some (4, 5, 3)) (.next ([945000000000, 9000000000000], [5760000000000]) (some (4, 5,
    3)) (some (4, 5, 3)) (.next ([660000000000, 9000000000000], [7920000000000]) (some (4, 5, 3))
    (some (4, 5, 3)) (.next ([0], [5835000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([-135000000000], [5760000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-420000000000],
    [7920000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-285000000000], [2160000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-420000000000], [2085000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-75000000000], [210000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-1845000000000], [5085000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-1770000000000], [4875000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2160000000000,
    9000000000000], [3990000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3930000000000],
    [6750000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next ([-3240000000000], [3990000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-5835000000000], [6915000000000, 9000000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-5760000000000], [6705000000000, 9000000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-7920000000000], [8580000000000, 9000000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5, 4)) (some (0, 5, 4)) (some (0, 5,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner3Part0 : FanWitness := (.next ([4680000000000], [4770000000000]) (some (6, 1, 3))
    (some (6, 1, 3)) (.next ([2160000000000, 9000000000000], [2745000000000, -9000000000000]) (some
    (6, 1, 3)) (some (6, 1, 3)) (.next ([1935000000000, 9000000000000], [2745000000000,
    -9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([1080000000000], [3825000000000])
    (some (6, 1, 3)) (some (6, 1, 4)) (.next ([1080000000000, 9000000000000], [4545000000000,
    -9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([855000000000], [3825000000000])
    (some (6, 1, 4)) (some (6, 1, 4)) (.next ([0, 9000000000000], [5040000000000]) (some (6, 1, 4))
    (some (6, 1, 4)) (.next ([0], [1080000000000, 9000000000000]) (some (6, 1, 4)) (some (6, 1, 4))
    (.next ([0, -9000000000000], [3825000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
    ([-135000000000], [2880000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-225000000000,
    -9000000000000], [3825000000000]) (some (6, 1, 4)) (some (6, 2, 4)) (.next ([-360000000000],
    [3105000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-1080000000000], [5040000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-1665000000000], [6705000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([-1080000000000], [3960000000000, -9000000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([-4545000000000], [9450000000000]) (some (6, 2, 4)) (some (6, 2, 4))
    (.next ([-1080000000000, -9000000000000], [2160000000000, 18000000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([-4770000000000], [9450000000000]) (some (6, 2, 4)) (some (6, 2, 4))
    (.next ([-2745000000000, 9000000000000], [4905000000000]) (some (6, 2, 4)) (some (6, 2, 4))
    (.next ([-2745000000000, 9000000000000], [4680000000000]) (some (6, 2, 4)) (some (6, 2, 4))
    (.next ([-3825000000000], [4905000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-4545000000000, 9000000000000], [5625000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-3825000000000], [4680000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-5040000000000,
    0], [5040000000000, 9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.terminal (some (6, 2,
    4)) (some (6, 2, 4)) (some (6, 2, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner0Part0 : FanWitness := (.next ([226800000000, -2610000000000], [5711400000000,
    5220000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([46800000000, -2610000000000],
    [5801400000000, 5220000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([0, 0], [939600000000,
    7830000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-86400000000, -5220000000000],
    [5398200000000, 2610000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-266400000000,
    -5220000000000], [5488200000000, 2610000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-313200000000, -2610000000000], [5801400000000, 5220000000000]) (some (7, 3, 5)) (some (7, 3,
    5)) (.next ([-45000000000], [720000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-313200000000, -2610000000000], [4861800000000, -2610000000000]) (some (7, 3, 5)) (some (7, 3,
    5)) (.next ([-626400000000, -5220000000000], [5488200000000, 2610000000000]) (some (7, 3, 5))
    (some (7, 3, 5)) (.next ([-4095000000000], [9675000000000]) (some (7, 3, 5)) (some (7, 3, 5))
    (.next ([-4635000000000], [10260000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-4815000000000], [10350000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-313200000000,
    -2610000000000], [626400000000, 5220000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-4186800000000, 2610000000000], [5893200000000, 2610000000000]) (some (7, 3, 5)) (some (7, 4,
    6)) (.next ([-4813200000000, -2610000000000], [6206400000000, 5220000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-4771800000000, 2610000000000], [5938200000000, 2610000000000]) (some
    (7, 4, 6)) (some (7, 4, 6)) (.next ([-4861800000000, 2610000000000], [5848200000000,
    2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5398200000000, -2610000000000],
    [6251400000000, 5220000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5126400000000,
    -5220000000000], [5893200000000, 2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-5488200000000, -2610000000000], [6161400000000, 5220000000000]) (some (7, 4, 6)) (some (7, 4,
    6)) (.next ([-4813200000000, -2610000000000], [5266800000000, -2610000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-4548600000000, 5220000000000], [4861800000000, -2610000000000]) (some
    (7, 4, 6)) (some (7, 4, 6)) (.next ([-5711400000000, -5220000000000], [5938200000000,
    2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5801400000000, -5220000000000],
    [5848200000000, 2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.terminal (some (7, 4, 6))
    (some (7, 4, 6)) (some (7, 4, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner3Part0 : FanWitness := (.next ([1080000000000, 9000000000000], [1080000000000,
    9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([2160000000000, 9000000000000],
    [2745000000000, -9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([1935000000000,
    9000000000000], [2745000000000, -9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
    ([1080000000000], [3825000000000]) (some (5, 6, 3)) (some (5, 6, 4)) (.next ([855000000000],
    [3825000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([645000000000], [3105000000000])
    (some (5, 6, 4)) (some (5, 6, 4)) (.next ([360000000000, 9000000000000], [5250000000000]) (some
    (5, 6, 4)) (some (5, 6, 4)) (.next ([0], [1080000000000, 9000000000000]) (some (5, 6, 4)) (some
    (5, 6, 4)) (.next ([0, -9000000000000], [3825000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-225000000000, -9000000000000], [3825000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-345000000000], [3450000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-720000000000], [5250000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-570000000000],
    [3675000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-720000000000], [4170000000000,
    -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2745000000000, 9000000000000],
    [9000000000000]) (some (0, 6, 4)) (some (1, 6, 4)) (.next ([-3825000000000], [9000000000000])
    (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-3825000000000], [7920000000000, -9000000000000])
    (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-1080000000000, -9000000000000], [2160000000000,
    18000000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-2745000000000, 9000000000000],
    [4905000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-2745000000000, 9000000000000],
    [4680000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-3825000000000], [4905000000000])
    (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-3825000000000], [4680000000000]) (some (1, 6, 4))
    (some (1, 6, 4)) (.next ([-3105000000000], [3750000000000]) (some (1, 6, 4)) (some (1, 6, 4))
    (.next ([-5250000000000, 0], [5610000000000, 9000000000000]) (some (1, 6, 4)) (some (6, 6, 4))
    (.terminal (some (6, 6, 4)) (some (6, 2, 4)) (some (6, 6, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner3Part0 : FanWitness := (.next ([4680000000000], [5250000000000]) (some (5, 1, 6))
    (some (5, 1, 6)) (.next ([2160000000000, 9000000000000], [2745000000000, -9000000000000]) (some
    (5, 1, 6)) (some (5, 1, 6)) (.next ([1935000000000, 9000000000000], [2745000000000,
    -9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1575000000000], [4680000000000])
    (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1575000000000], [4905000000000]) (some (5, 1, 6))
    (some (5, 1, 6)) (.next ([1080000000000], [3825000000000]) (some (5, 1, 6)) (some (5, 1, 6))
    (.next ([855000000000], [3825000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
    ([360000000000, 9000000000000], [5250000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0],
    [1080000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, -9000000000000],
    [3825000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-225000000000, -9000000000000],
    [3825000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-345000000000], [3450000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-720000000000], [5250000000000]) (some (0, 1, 6))
    (some (0, 2, 6)) (.next ([-570000000000], [3675000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-1080000000000, -9000000000000], [6480000000000, 9000000000000]) (some (0, 2, 6)) (some
    (0, 2, 6)) (.next ([-1080000000000, -9000000000000], [2160000000000, 18000000000000]) (some (0,
    2, 6)) (some (1, 2, 6)) (.next ([-5250000000000], [9930000000000]) (some (1, 2, 6)) (some (1, 2,
    6)) (.next ([-2745000000000, 9000000000000], [4905000000000]) (some (1, 2, 6)) (some (1, 2, 6))
    (.next ([-2745000000000, 9000000000000], [4680000000000]) (some (1, 2, 6)) (some (1, 2, 6))
    (.next ([-4680000000000], [6255000000000]) (some (1, 2, 6)) (some (1, 2, 6)) (.next
    ([-4905000000000], [6480000000000]) (some (1, 2, 6)) (some (1, 2, 6)) (.next ([-3825000000000],
    [4905000000000]) (some (1, 2, 6)) (some (1, 6, 6)) (.next ([-3825000000000], [4680000000000])
    (some (1, 6, 6)) (some (1, 6, 6)) (.next ([-5250000000000, 0], [5610000000000, 9000000000000])
    (some (1, 6, 6)) (some (1, 6, 6)) (.terminal (some (1, 6, 6)) (some (1, 6, 4)) (some (1, 6,
    6)))))))))))))))))))))))))))

theorem excluded16_0 : ExcludedOn (model16.B 0 ++ [step16.q]) 9000000000000 (model16.caps 0)
    (model16.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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

theorem excluded16_4 : ExcludedOn (model16.B 4 ++ [step16.q]) 9000000000000 (model16.caps 4)
    (model16.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5625000000000], [135000000000]) (some (5, 0, 1))
      (some (5, 1, 1)) (.next ([135000000000], [75000000000]) (some (5, 1, 1)) (some (5, 1, 1))
      (.next ([3240000000000], [1845000000000]) (some (5, 1, 1)) (some (5, 1, 2))
      fan16Owner4Part0)))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_8 : ExcludedOn (model16.B 8 ++ [step16.q]) 9000000000000 (model16.caps 8)
    (model16.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5625000000000], [135000000000]) (some (0, 0, 4))
      (some (0, 1, 4)) (.next ([4320000000000], [585000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([4275000000000], [765000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([135000000000], [45000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([5040000000000],
      [3180000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([5040000000000], [5040000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([1860000000000], [3945000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([1725000000000], [3900000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([0], [5805000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-135000000000],
      [5760000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-585000000000], [4905000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-765000000000], [5040000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-45000000000], [180000000000]) (some (0, 1, 4)) (some (0, 4, 4))
      (.next ([-3180000000000], [8220000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.next
      ([-5040000000000], [10080000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-3945000000000], [5805000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-3900000000000], [5625000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4,
      3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded16_2
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_1 : ExcludedOn (model17.B 1 ++ [step17.q]) 9000000000000 (model17.caps 1)
    (model17.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_2 : ExcludedOn (model17.B 2 ++ [step17.q]) 9000000000000 (model17.caps 2)
    (model17.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6255000000000, 9000000000000], [3825000000000,
      -9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([5175000000000], [4905000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1080000000000, 9000000000000], [1080000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4095000000000, -9000000000000],
      [4905000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0, 0], [1080000000000,
      9000000000000]) (some (0, 3, 1)) (some (3, 3, 1)) (.next ([-3825000000000, 9000000000000],
      [10080000000000, 0]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([-4905000000000],
      [10080000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1080000000000, -9000000000000],
      [2160000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-4905000000000,
      0], [9000000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded17_4 : ExcludedOn (model17.B 4 ++ [step17.q]) 9000000000000 (model17.caps 4)
    (model17.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_5 : ExcludedOn (model17.B 5 ++ [step17.q]) 9000000000000 (model17.caps 5)
    (model17.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded17_8 : ExcludedOn (model17.B 8 ++ [step17.q]) 9000000000000 (model17.caps 8)
    (model17.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded17_4
    · exact excluded17_5
    · exact excluded17_6
    · exact excluded17_7
    · exact excluded17_8
    · exact excluded17_9
theorem next17 : model17.insert step17 = model18 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded18_0 : ExcludedOn (model18.B 0 ++ [step18.q]) 9000000000000 (model18.caps 0)
    (model18.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_1 : ExcludedOn (model18.B 1 ++ [step18.q]) 9000000000000 (model18.caps 1)
    (model18.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_2 : ExcludedOn (model18.B 2 ++ [step18.q]) 9000000000000 (model18.caps 2)
    (model18.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6255000000000, 9000000000000], [3600000000000,
      -9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([5175000000000], [4680000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1080000000000, 9000000000000], [1080000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4095000000000, -9000000000000],
      [4680000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0, 0], [1080000000000,
      9000000000000]) (some (0, 3, 1)) (some (3, 3, 1)) (.next ([-3600000000000, 9000000000000],
      [9855000000000, 0]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([-4680000000000],
      [9855000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1080000000000, -9000000000000],
      [2160000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-4680000000000,
      0], [8775000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_4 : ExcludedOn (model18.B 4 ++ [step18.q]) 9000000000000 (model18.caps 4)
    (model18.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_5 : ExcludedOn (model18.B 5 ++ [step18.q]) 9000000000000 (model18.caps 5)
    (model18.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded18_8 : ExcludedOn (model18.B 8 ++ [step18.q]) 9000000000000 (model18.caps 8)
    (model18.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded18_0
    · exact excluded18_1
    · exact excluded18_2
    · exact (hj rfl).elim
    · exact excluded18_4
    · exact excluded18_5
    · exact excluded18_6
    · exact excluded18_7
    · exact excluded18_8
    · exact excluded18_9
theorem next18 : model18.insert step18 = model19 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded19_0 : ExcludedOn (model19.B 0 ++ [step19.q]) 9000000000000 (model19.caps 0)
    (model19.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5311800000000, -2610000000000], [86400000000,
      5220000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([5221800000000, -2610000000000],
      [266400000000, 5220000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([675000000000],
      [45000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([6165000000000], [1875000000000])
      (some (6, 7, 4)) (some (6, 7, 4)) (.next ([6255000000000], [1965000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([5580000000000], [1920000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([313200000000, 2610000000000], [313200000000, 2610000000000]) (some (6, 7, 4)) (some
      (6, 7, 4)) (.next ([1706400000000, 5220000000000], [4186800000000, -2610000000000]) (some (0,
      7, 4)) (some (0, 7, 4)) (.next ([1393200000000, 2610000000000], [4813200000000,
      2610000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([1166400000000, 5220000000000],
      [4771800000000, -2610000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([986400000000,
      5220000000000], [4861800000000, -2610000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
      ([1393200000000, 2610000000000], [7813200000000, 2610000000000]) (some (0, 7, 4)) (some (0, 7,
      5)) (.next ([853200000000, 2610000000000], [5398200000000, 2610000000000]) (some (0, 7, 5))
      (some (0, 7, 5)) (.next ([766800000000, -2610000000000], [5126400000000, 5220000000000]) (some
      (0, 7, 5)) (some (0, 7, 5)) (.next ([673200000000, 2610000000000], [5488200000000,
      2610000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([766800000000, -2610000000000],
      [7186800000000, -2610000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([766800000000,
      -2610000000000], [8126400000000, 5220000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
      ([453600000000, -5220000000000], [4813200000000, 2610000000000]) (some (0, 7, 5)) (some (0, 7,
      5)) (.next ([453600000000, -5220000000000], [7813200000000, 2610000000000]) (some (0, 7, 5))
      (some (0, 7, 5)) fan19Owner0Part0)))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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

theorem excluded19_3 : ExcludedOn (model19.B 3 ++ [step19.q]) 9000000000000 (model19.caps 3)
    (model19.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_4 : ExcludedOn (model19.B 4 ++ [step19.q]) 9000000000000 (model19.caps 4)
    (model19.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5625000000000], [135000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) (.next ([7500000000000], [420000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([1875000000000], [285000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      fan19Owner4Part0)))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_6 : ExcludedOn (model19.B 6 ++ [step19.q]) 9000000000000 (model19.caps 6)
    (model19.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_7 : ExcludedOn (model19.B 7 ++ [step19.q]) 9000000000000 (model19.caps 7)
    (model19.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_8 : ExcludedOn (model19.B 8 ++ [step19.q]) 9000000000000 (model19.caps 8)
    (model19.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded19_0
    · exact excluded19_1
    · exact excluded19_2
    · exact excluded19_3
    · exact excluded19_4
    · exact (hj rfl).elim
    · exact excluded19_6
    · exact excluded19_7
    · exact excluded19_8
    · exact excluded19_9
theorem next19 : model19.insert step19 = model20 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded20_0 : ExcludedOn (model20.B 0 ++ [step20.q]) 9000000000000 (model20.caps 0)
    (model20.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded20_3 : ExcludedOn (model20.B 3 ++ [step20.q]) 9000000000000 (model20.caps 3)
    (model20.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3825000000000, -9000000000000], [0,
      9000000000000]) (some (4, 6, 2)) (some (6, 6, 3)) (.next ([2745000000000], [135000000000])
      (some (6, 6, 3)) (some (6, 6, 3)) (.next ([3600000000000, -9000000000000], [225000000000,
      9000000000000]) (some (6, 6, 3)) (some (6, 6, 3)) (.next ([2745000000000], [360000000000])
      (some (6, 6, 3)) (some (6, 6, 3)) (.next ([3960000000000], [1080000000000]) (some (6, 6, 3))
      (some (6, 6, 3)) (.next ([5040000000000], [1665000000000]) (some (6, 6, 3)) (some (6, 6, 3))
      (.next ([2880000000000, -9000000000000], [1080000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      (.next ([4905000000000], [4545000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
      ([1080000000000, 9000000000000], [1080000000000, 9000000000000]) (some (6, 1, 3)) (some (6, 1,
      3)) fan20Owner3Part0)))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_4 : ExcludedOn (model20.B 4 ++ [step20.q]) 9000000000000 (model20.caps 4)
    (model20.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded20_0
    · exact excluded20_1
    · exact excluded20_2
    · exact excluded20_3
    · exact excluded20_4
    · exact excluded20_5
    · exact excluded20_6
    · exact excluded20_7
    · exact (hj rfl).elim
    · exact excluded20_9
theorem next20 : model20.insert step20 = model21 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded21_0 : ExcludedOn (model21.B 0 ++ [step21.q]) 9000000000000 (model21.caps 0)
    (model21.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_1 : ExcludedOn (model21.B 1 ++ [step21.q]) 9000000000000 (model21.caps 1)
    (model21.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_2 : ExcludedOn (model21.B 2 ++ [step21.q]) 9000000000000 (model21.caps 2)
    (model21.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_4 : ExcludedOn (model21.B 4 ++ [step21.q]) 9000000000000 (model21.caps 4)
    (model21.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5625000000000], [135000000000]) (some (5, 0, 1))
      (some (5, 1, 1)) (.next ([135000000000], [75000000000]) (some (5, 1, 1)) (some (5, 1, 1))
      (.next ([3240000000000], [1845000000000]) (some (5, 1, 1)) (some (5, 1, 2)) (.next
      ([3105000000000], [1770000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1830000000000,
      9000000000000], [2160000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next
      ([1230000000000], [3270000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([720000000000],
      [2670000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 5)) (.next ([750000000000],
      [3240000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1080000000000, 9000000000000],
      [5835000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([945000000000, 9000000000000],
      [5760000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0], [5835000000000]) (some (4, 1,
      5)) (some (4, 1, 5)) (.next ([-135000000000], [5760000000000]) (some (0, 1, 5)) (some (0, 1,
      5)) (.next ([-75000000000], [210000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-1845000000000], [5085000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-1770000000000], [4875000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2160000000000,
      9000000000000], [3990000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3270000000000],
      [4500000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2670000000000, 9000000000000],
      [3390000000000, -9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3240000000000],
      [3990000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5835000000000], [6915000000000,
      9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5760000000000], [6705000000000,
      9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.terminal (some (0, 1, 5)) (some (0, 1, 5))
      (some (0, 1, 5))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5625000000000], [135000000000]) (some (0, 0, 4))
      (some (0, 1, 4)) (.next ([3960000000000], [375000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([3915000000000], [555000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([5250000000000], [1095000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([135000000000],
      [45000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([3375000000000], [2430000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([3240000000000], [2385000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([5250000000000], [4470000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([0], [5805000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-135000000000],
      [5760000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-375000000000], [4335000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-555000000000], [4470000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-1095000000000], [6345000000000]) (some (0, 1, 4)) (some (0, 4, 4))
      (.next ([-45000000000], [180000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-2430000000000], [5805000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-2385000000000], [5625000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-4470000000000], [9720000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4,
      3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded21_9 : ExcludedOn (model21.B 9 ++ [step21.q]) 9000000000000 (model21.caps 9)
    (model21.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5311800000000, -2610000000000], [86400000000,
      5220000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([5221800000000, -2610000000000],
      [266400000000, 5220000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([5488200000000,
      2610000000000], [313200000000, 2610000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([675000000000], [45000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([4548600000000,
      -5220000000000], [313200000000, 2610000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([4861800000000, -2610000000000], [626400000000, 5220000000000]) (some (6, 7, 4)) (some (6, 7,
      4)) (.next ([5580000000000], [4095000000000]) (some (6, 7, 4)) (some (7, 7, 4)) (.next
      ([5625000000000], [4635000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([5535000000000],
      [4815000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([313200000000, 2610000000000],
      [313200000000, 2610000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([1706400000000,
      5220000000000], [4186800000000, -2610000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next
      ([1393200000000, 2610000000000], [4813200000000, 2610000000000]) (some (7, 2, 4)) (some (7, 2,
      4)) (.next ([1166400000000, 5220000000000], [4771800000000, -2610000000000]) (some (7, 2, 4))
      (some (7, 2, 4)) (.next ([986400000000, 5220000000000], [4861800000000, -2610000000000]) (some
      (7, 2, 4)) (some (7, 2, 4)) (.next ([853200000000, 2610000000000], [5398200000000,
      2610000000000]) (some (7, 2, 4)) (some (7, 2, 5)) (.next ([766800000000, -2610000000000],
      [5126400000000, 5220000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([673200000000,
      2610000000000], [5488200000000, 2610000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
      ([453600000000, -5220000000000], [4813200000000, 2610000000000]) (some (7, 2, 5)) (some (7, 2,
      5)) (.next ([313200000000, 2610000000000], [4548600000000, -5220000000000]) (some (7, 2, 5))
      (some (7, 3, 5)) fan22Owner0Part0)))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([3825000000000, -9000000000000], [0,
      9000000000000]) (some (4, 6, 2)) (some (5, 6, 3)) (.next ([3600000000000, -9000000000000],
      [225000000000, 9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([3105000000000],
      [345000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([4530000000000], [720000000000])
      (some (5, 6, 3)) (some (5, 6, 3)) (.next ([3105000000000], [570000000000]) (some (5, 6, 3))
      (some (5, 6, 3)) (.next ([3450000000000, -9000000000000], [720000000000]) (some (5, 6, 3))
      (some (5, 6, 3)) (.next ([6255000000000, 9000000000000], [2745000000000, -9000000000000])
      (some (5, 6, 3)) (some (5, 6, 3)) (.next ([5175000000000], [3825000000000]) (some (5, 6, 3))
      (some (5, 6, 3)) (.next ([4095000000000, -9000000000000], [3825000000000]) (some (5, 6, 3))
      (some (5, 6, 3)) fan22Owner3Part0)))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel)
      0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_5 : ExcludedOn (model22.B 5 ++ [step22.q]) 9000000000000 (model22.caps 5)
    (model22.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_6 : ExcludedOn (model22.B 6 ++ [step22.q]) 9000000000000 (model22.caps 6)
    (model22.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded22_5
    · exact excluded22_6
    · exact excluded22_7
    · exact excluded22_8
    · exact excluded22_9
theorem next22 : model22.insert step22 = model23 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded23_0 : ExcludedOn (model23.B 0 ++ [step23.q]) 9000000000000 (model23.caps 0)
    (model23.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_1 : ExcludedOn (model23.B 1 ++ [step23.q]) 9000000000000 (model23.caps 1)
    (model23.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_3 : ExcludedOn (model23.B 3 ++ [step23.q]) 9000000000000 (model23.caps 3)
    (model23.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3825000000000, -9000000000000], [0,
      9000000000000]) (some (4, 1, 6)) (some (5, 1, 6)) (.next ([3600000000000, -9000000000000],
      [225000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([3105000000000],
      [345000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([4530000000000], [720000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([3105000000000], [570000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([5400000000000], [1080000000000, 9000000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([1080000000000, 9000000000000], [1080000000000, 9000000000000]) (some
      (5, 1, 6)) (some (5, 1, 6)) fan23Owner3Part0)))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded23_4 : ExcludedOn (model23.B 4 ++ [step23.q]) 9000000000000 (model23.caps 4)
    (model23.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_5 : ExcludedOn (model23.B 5 ++ [step23.q]) 9000000000000 (model23.caps 5)
    (model23.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded23_8 : ExcludedOn (model23.B 8 ++ [step23.q]) 9000000000000 (model23.caps 8)
    (model23.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_9 : ExcludedOn (model23.B 9 ++ [step23.q]) 9000000000000 (model23.caps 9)
    (model23.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded23_3
    · exact excluded23_4
    · exact excluded23_5
    · exact excluded23_6
    · exact excluded23_7
    · exact excluded23_8
    · exact excluded23_9
theorem next23 : model23.insert step23 = model24 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext120000130000
end ConwaySoifer.Simplified.Certificates
