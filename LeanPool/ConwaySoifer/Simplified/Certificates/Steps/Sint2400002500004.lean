/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint240000250000
import Mathlib.Tactic.FinCases

/-!
# Sint 240000 250000 4

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
namespace Sint240000250000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner5Part0 : FanWitness := (.next ([4845000000000, 0], [1440000000000, 9000000000000])
    (some (3, 1, 5)) (some (3, 1, 5)) (.next ([4125000000000], [1770000000000]) (some (3, 1, 5))
    (some (3, 1, 5)) (.next ([1080000000000, -9000000000000], [510000000000]) (some (3, 1, 5)) (some
    (4, 1, 5)) (.next ([4455000000000, -9000000000000], [2160000000000, 9000000000000]) (some (4, 1,
    5)) (some (4, 1, 5)) (.next ([4215000000000, 0], [2160000000000, 9000000000000]) (some (4, 1,
    5)) (some (4, 1, 5)) (.next ([4215000000000], [2400000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([4335000000000], [3030000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([3705000000000], [3750000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2865000000000],
    [3240000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([720000000000], [4125000000000])
    (some (4, 1, 3)) (some (4, 1, 3)) (.next ([90000000000], [630000000000]) (some (4, 1, 3)) (some
    (4, 1, 3)) (.next ([0], [4215000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-510000000000], [3750000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-1440000000000,
    -9000000000000], [6285000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([-1770000000000], [5895000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-510000000000,
    0], [1590000000000, -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2160000000000,
    -9000000000000], [6615000000000]) (some (0, 2, 3)) (some (0, 5, 3)) (.next ([-2160000000000,
    -9000000000000], [6375000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-2400000000000], [6615000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3030000000000],
    [7365000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3750000000000], [7455000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3240000000000], [6105000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-4125000000000], [4845000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-630000000000], [720000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0,
    5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner9Part0 : FanWitness := (.next ([3000000000000], [2160000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([3750000000000], [5760000000000]) (some (5, 1, 2)) (some (5, 1, 2))
    (.next ([405000000000], [720000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([1110000000000], [2490000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([705000000000],
    [1770000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([900000000000], [3240000000000])
    (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1230000000000], [4635000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([750000000000], [3600000000000]) (some (5, 1, 2)) (some (5, 1, 2))
    (.next ([495000000000], [2520000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([510000000000], [5760000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([0],
    [4140000000000]) (some (5, 1, 2)) (some (5, 1, 5)) (.next ([-210000000000], [750000000000])
    (some (5, 1, 5)) (some (5, 1, 5)) (.next ([-1620000000000], [5370000000000]) (some (5, 1, 5))
    (some (5, 1, 5)) (.next ([-1125000000000], [3645000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-2160000000000], [5160000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-5760000000000], [9510000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-720000000000],
    [1125000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2490000000000], [3600000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1770000000000], [2475000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-3240000000000], [4140000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-4635000000000], [5865000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-3600000000000], [4350000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2520000000000],
    [3015000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5760000000000], [6270000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.terminal (some (0, 1, 5)) (some (0, 1, 5)) (some (0, 1,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner5Part0 : FanWitness := (.next ([1215000000000, -9000000000000], [225000000000]) (some
    (3, 1, 5)) (some (3, 1, 5)) (.next ([4845000000000, 0], [1440000000000, 9000000000000]) (some
    (3, 1, 5)) (some (3, 1, 5)) (.next ([4125000000000], [1770000000000]) (some (3, 1, 5)) (some (3,
    1, 5)) (.next ([4455000000000, -9000000000000], [2160000000000, 9000000000000]) (some (3, 1, 5))
    (some (4, 1, 5)) (.next ([4215000000000, 0], [2160000000000, 9000000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([4215000000000], [2400000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([4620000000000], [2880000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([3990000000000], [3600000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([3015000000000],
    [3375000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([720000000000], [4125000000000])
    (some (4, 1, 3)) (some (4, 1, 3)) (.next ([90000000000], [630000000000]) (some (4, 1, 3)) (some
    (4, 1, 3)) (.next ([0], [4215000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-225000000000], [3600000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-225000000000, 0],
    [1440000000000, -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1440000000000,
    -9000000000000], [6285000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 5, 3)) (.next
    ([-1770000000000], [5895000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2160000000000,
    -9000000000000], [6615000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2160000000000,
    -9000000000000], [6375000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-2400000000000], [6615000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2880000000000],
    [7500000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3600000000000], [7590000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3375000000000], [6390000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-4125000000000], [4845000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-630000000000], [720000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0,
    5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan36Owner4Part0 : FanWitness := (.next ([1785000000000], [1095000000000]) (some (5, 6, 3))
    (some (5, 6, 3)) (.next ([4215000000000], [4170000000000]) (some (5, 6, 3)) (some (5, 6, 3))
    (.next ([2310000000000], [2565000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
    ([2160000000000], [3090000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([1995000000000,
    -9000000000000], [2880000000000, 9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
    ([1080000000000], [2010000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([1605000000000],
    [4875000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([1125000000000], [5250000000000])
    (some (5, 6, 3)) (some (5, 6, 3)) (.next ([0, 0], [2160000000000, 9000000000000]) (some (5, 6,
    3)) (some (5, 6, 3)) (.next ([-15000000000], [4890000000000]) (some (0, 6, 3)) (some (0, 6, 4))
    (.next ([-660000000000], [6480000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-555000000000, -9000000000000], [4875000000000, 0]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-720000000000], [4875000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-660000000000],
    [4155000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-555000000000], [1785000000000])
    (some (0, 6, 4)) (some (0, 6, 5)) (.next ([-2160000000000, -9000000000000], [6375000000000,
    9000000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-1095000000000], [2880000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-4170000000000], [8385000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-2565000000000], [4875000000000]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-3090000000000], [5250000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([-2880000000000, -9000000000000], [4875000000000, 0]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([-2010000000000], [3090000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-4875000000000],
    [6480000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-5250000000000], [6375000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.terminal (some (0, 3, 5)) (some (0, 3, 5)) (some (0, 3,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner3Part0 : FanWitness := (.next ([5400000000000], [1785000000000, 9000000000000]) (some
    (4, 5, 3)) (some (4, 5, 3)) (.next ([5505000000000], [2160000000000, 9000000000000]) (some (4,
    5, 3)) (some (4, 5, 3)) (.next ([1770000000000], [750000000000]) (some (4, 5, 3)) (some (4, 5,
    3)) (.next ([4650000000000], [2145000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([4755000000000], [2520000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([360000000000,
    -9000000000000], [390000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([105000000000], [375000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([1815000000000],
    [7185000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([375000000000], [5025000000000])
    (some (4, 5, 3)) (some (4, 5, 3)) (.next ([45000000000], [6435000000000]) (some (4, 5, 3)) (some
    (4, 5, 3)) (.next ([0], [2160000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([-345000000000, -9000000000000], [7185000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-1680000000000], [9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1785000000000],
    [8625000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1785000000000, -9000000000000],
    [7185000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2160000000000,
    -9000000000000], [7665000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-750000000000], [2520000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2145000000000],
    [6795000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2520000000000], [7275000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-390000000000, -9000000000000], [750000000000]) (some
    (0, 5, 3)) (some (0, 5, 3)) (.next ([-375000000000], [480000000000]) (some (0, 5, 3)) (some (0,
    5, 3)) (.next ([-7185000000000], [9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-5025000000000], [5400000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-6435000000000],
    [6480000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3)) (some (0, 5, 3))
    (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner4Part0 : FanWitness := (.next ([1935000000000], [2160000000000]) (some (5, 1, 6))
    (some (5, 1, 6)) (.next ([2160000000000], [3090000000000]) (some (5, 1, 6)) (some (5, 1, 6))
    (.next ([1995000000000, -9000000000000], [2880000000000, 9000000000000]) (some (5, 1, 6)) (some
    (5, 1, 6)) (.next ([705000000000], [1605000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
    ([1605000000000], [4875000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([720000000000],
    [2310000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1125000000000], [5250000000000])
    (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, 0], [2160000000000, 9000000000000]) (some (5, 1,
    6)) (some (5, 1, 6)) (.next ([0, -9000000000000], [3090000000000, 0]) (some (0, 1, 6)) (some (0,
    1, 6)) (.next ([-660000000000], [6480000000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next
    ([-555000000000, -9000000000000], [4875000000000, 0]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-720000000000], [4875000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-660000000000],
    [4155000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-2160000000000, -9000000000000],
    [7185000000000, 0]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-2160000000000, -9000000000000],
    [6375000000000, 9000000000000]) (some (0, 2, 6)) (some (0, 3, 6)) (.next ([-1095000000000],
    [2880000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-2970000000000], [7185000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-2160000000000], [4095000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([-3090000000000], [5250000000000]) (some (0, 3, 5)) (some (0, 3, 5))
    (.next ([-2880000000000, -9000000000000], [4875000000000, 0]) (some (0, 3, 5)) (some (0, 3, 5))
    (.next ([-1605000000000], [2310000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([-4875000000000], [6480000000000]) (some (0, 3, 5)) (some (0, 6, 5)) (.next ([-2310000000000],
    [3030000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-5250000000000], [6375000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.terminal (some (0, 6, 5)) (some (0, 6, 5)) (some (0, 6,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan38Owner6Part0 : FanWitness := (.next ([-1935000000000, -9000000000000], [7560000000000,
    9000000000000]) (some (0, 5, 8)) (some (0, 5, 8)) (.next ([-240000000000], [888000000000]) (some
    (0, 5, 8)) (some (0, 5, 8)) (.next ([-2160000000000], [7785000000000]) (some (0, 5, 8)) (some
    (1, 5, 8)) (.next ([-855000000000], [2865000000000]) (some (1, 5, 8)) (some (1, 5, 8)) (.next
    ([-615000000000], [1977000000000]) (some (1, 5, 8)) (some (1, 5, 8)) (.next ([-990000000000],
    [3150000000000]) (some (1, 5, 8)) (some (2, 5, 8)) (.next ([-750000000000], [2262000000000])
    (some (2, 5, 8)) (some (2, 5, 8)) (.next ([-1728000000000, 9000000000000], [4215000000000,
    -9000000000000]) (some (2, 5, 8)) (some (2, 5, 8)) (.next ([-135000000000], [285000000000])
    (some (2, 5, 8)) (some (2, 5, 8)) (.next ([-3240000000000], [6615000000000]) (some (2, 5, 8))
    (some (3, 5, 8)) (.next ([-2160000000000, -9000000000000], [4320000000000, 18000000000000])
    (some (3, 5, 8)) (some (3, 5, 8)) (.next ([-2385000000000, 0], [4545000000000, 9000000000000])
    (some (3, 5, 8)) (some (3, 5, 8)) (.next ([-3765000000000, -9000000000000], [6480000000000])
    (some (3, 5, 8)) (some (3, 5, 8)) (.next ([-3888000000000], [6375000000000]) (some (3, 5, 8))
    (some (3, 5, 8)) (.next ([-3990000000000], [6480000000000]) (some (3, 5, 8)) (some (3, 5, 8))
    (.next ([-5400000000000, -9000000000000], [6615000000000]) (some (3, 5, 7)) (some (3, 5, 7))
    (.next ([-5625000000000], [6615000000000]) (some (3, 5, 7)) (some (3, 5, 7)) (.next
    ([-3090000000000, 9000000000000], [3600000000000, -9000000000000]) (some (3, 5, 7)) (some (3, 5,
    7)) (.next ([-4320000000000, 9000000000000], [4875000000000]) (some (3, 5, 7)) (some (3, 5, 7))
    (.next ([-5250000000000], [5760000000000]) (some (3, 5, 7)) (some (3, 5, 7)) (.next
    ([-1500000000000], [1635000000000]) (some (3, 5, 7)) (some (3, 5, 7)) (.next ([-3240000000000,
    9000000000000], [3465000000000, -9000000000000]) (some (3, 5, 7)) (some (3, 5, 7)) (.next
    ([-6048000000000, -9000000000000], [6375000000000]) (some (3, 5, 7)) (some (3, 5, 7)) (.next
    ([-6273000000000], [6375000000000]) (some (3, 5, 7)) (some (3, 5, 7)) (.terminal (some (3, 5,
    7)) (some (3, 5, 7)) (some (3, 5, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan38Owner6Part1 : FanWitness := (.next ([2487000000000, 0], [1728000000000, -9000000000000])
    (some (7, 3, 8)) (some (7, 3, 8)) (.next ([150000000000], [135000000000]) (some (7, 3, 8)) (some
    (7, 3, 8)) (.next ([3375000000000], [3240000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next
    ([2160000000000, 9000000000000], [2160000000000, 9000000000000]) (some (7, 3, 8)) (some (7, 3,
    8)) (.next ([2160000000000, 9000000000000], [2385000000000]) (some (7, 3, 8)) (some (7, 3, 8))
    (.next ([2715000000000, -9000000000000], [3765000000000, 9000000000000]) (some (7, 3, 8)) (some
    (7, 3, 8)) (.next ([2487000000000], [3888000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next
    ([2490000000000], [3990000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([1215000000000,
    -9000000000000], [5400000000000, 9000000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next
    ([990000000000], [5625000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([510000000000, 0],
    [3090000000000, -9000000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([555000000000,
    9000000000000], [4320000000000, -9000000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next
    ([510000000000], [5250000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([135000000000],
    [1500000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([225000000000, 0], [3240000000000,
    -9000000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([327000000000, -9000000000000],
    [6048000000000, 9000000000000]) (some (0, 3, 8)) (some (0, 4, 8)) (.next ([102000000000],
    [6273000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next ([0, 0], [2160000000000,
    9000000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next ([-105000000000], [2388000000000])
    (some (0, 4, 8)) (some (0, 5, 8)) (.next ([-720000000000], [4365000000000]) (some (0, 5, 8))
    (some (0, 5, 8)) (.next ([-855000000000], [4650000000000]) (some (0, 5, 8)) (some (0, 5, 8))
    (.next ([-1650000000000, -9000000000000], [7410000000000, 9000000000000]) (some (0, 5, 8)) (some
    (0, 5, 8)) (.next ([-1875000000000], [7635000000000]) (some (0, 5, 8)) (some (0, 5, 8)) (.next
    ([-1605000000000], [6480000000000]) (some (0, 5, 8)) (some (0, 5, 8))
    fan38Owner6Part0))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_5 : ExcludedOn (model32.B 5 ++ [step32.q]) 9000000000000 (model32.caps 5)
    (model32.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4845000000000, 0], [1440000000000,
      9000000000000]) (some (3, 0, 5)) (some (3, 1, 5)) (.next ([4125000000000], [1770000000000])
      (some (3, 1, 5)) (some (3, 1, 5)) (.next ([4455000000000, -9000000000000], [2160000000000,
      9000000000000]) (some (3, 1, 5)) (some (4, 1, 5)) (.next ([4215000000000, 0], [2160000000000,
      9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([4215000000000], [2400000000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2625000000000], [2487000000000]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([1503000000000], [2625000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([2358000000000], [4392000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([1728000000000], [5112000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([720000000000],
      [4125000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([90000000000], [630000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0], [4215000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([-1440000000000, -9000000000000], [6285000000000, 9000000000000]) (some (0, 1, 3))
      (some (0, 2, 3)) (.next ([-1770000000000], [5895000000000]) (some (0, 2, 3)) (some (0, 2, 3))
      (.next ([-2160000000000, -9000000000000], [6615000000000]) (some (0, 2, 3)) (some (0, 2, 3))
      (.next ([-2160000000000, -9000000000000], [6375000000000, 9000000000000]) (some (0, 2, 3))
      (some (0, 2, 3)) (.next ([-2400000000000], [6615000000000]) (some (0, 2, 3)) (some (0, 2, 3))
      (.next ([-2487000000000], [5112000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-2625000000000], [4128000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-4392000000000], [6750000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-5112000000000], [6840000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-4125000000000], [4845000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-630000000000],
      [720000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 5, 3)) (some (0, 5, 3))
      (some (0, 5, 3))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded32_7
    · exact excluded32_8
    · exact excluded32_9
theorem next32 : model32.insert step32 = model33 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded33_0 : ExcludedOn (model33.B 0 ++ [step33.q]) 9000000000000 (model33.caps 0)
    (model33.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_4 : ExcludedOn (model33.B 4 ++ [step33.q]) 9000000000000 (model33.caps 4)
    (model33.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_5 : ExcludedOn (model33.B 5 ++ [step33.q]) 9000000000000 (model33.caps 5)
    (model33.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3240000000000], [510000000000]) (some (3, 0, 5))
      (some (3, 1, 5)) fan33Owner5Part0)) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([540000000000], [210000000000]) (some (5, 0, 1))
      (some (5, 1, 2)) (.next ([3750000000000], [1620000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([2520000000000], [1125000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      fan33Owner9Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded33_5
    · exact (hj rfl).elim
    · exact excluded33_7
    · exact excluded33_8
    · exact excluded33_9
theorem next33 : model33.insert step33 = model34 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded34_0 : ExcludedOn (model34.B 0 ++ [step34.q]) 9000000000000 (model34.caps 0)
    (model34.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_1 : ExcludedOn (model34.B 1 ++ [step34.q]) 9000000000000 (model34.caps 1)
    (model34.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_3 : ExcludedOn (model34.B 3 ++ [step34.q]) 9000000000000 (model34.caps 3)
    (model34.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_4 : ExcludedOn (model34.B 4 ++ [step34.q]) 9000000000000 (model34.caps 4)
    (model34.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4845000000000, 0], [1440000000000,
      9000000000000]) (some (3, 0, 5)) (some (3, 5, 5)) (.next ([4125000000000], [1770000000000])
      (some (3, 5, 5)) (some (3, 5, 5)) (.next ([4455000000000, -9000000000000], [2160000000000,
      9000000000000]) (some (3, 5, 5)) (some (4, 5, 5)) (.next ([4215000000000, 0], [2160000000000,
      9000000000000]) (some (4, 5, 5)) (some (4, 5, 5)) (.next ([4215000000000], [2400000000000])
      (some (4, 5, 3)) (some (4, 5, 3)) (.next ([720000000000], [4125000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([90000000000], [630000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([720000000000], [7500000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0],
      [4215000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1440000000000, -9000000000000],
      [6285000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1770000000000],
      [5895000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2160000000000, -9000000000000],
      [6615000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2160000000000, -9000000000000],
      [6375000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2400000000000],
      [6615000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4125000000000], [4845000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-630000000000], [720000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-7500000000000], [8220000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded34_4
    · exact excluded34_5
    · exact excluded34_6
    · exact excluded34_7
    · exact excluded34_8
    · exact (hj rfl).elim
theorem next34 : model34.insert step34 = model35 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded35_0 : ExcludedOn (model35.B 0 ++ [step35.q]) 9000000000000 (model35.caps 0)
    (model35.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_5 : ExcludedOn (model35.B 5 ++ [step35.q]) 9000000000000 (model35.caps 5)
    (model35.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000], [225000000000]) (some (3, 0, 5))
      (some (3, 1, 5)) fan35Owner5Part0)) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([2385000000000], [3240000000000]) (some (3, 0,
      1)) (some (3, 1, 2)) (.next ([3600000000000], [5625000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([360000000000], [5625000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [5625000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-3240000000000], [5625000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-5625000000000], [9225000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-5625000000000], [5985000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.terminal (some (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded35_5
    · exact (hj rfl).elim
    · exact excluded35_7
    · exact excluded35_8
    · exact excluded35_9
theorem next35 : model35.insert step35 = model36 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded36_0 : ExcludedOn (model36.B 0 ++ [step36.q]) 9000000000000 (model36.caps 0)
    (model36.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4875000000000], [15000000000]) (some (5, 0, 3))
      (some (5, 6, 3)) (.next ([5820000000000], [660000000000]) (some (5, 6, 3)) (some (5, 6, 3))
      (.next ([4320000000000, -9000000000000], [555000000000, 9000000000000]) (some (5, 6, 3)) (some
      (5, 6, 3)) (.next ([4155000000000], [720000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([3495000000000], [660000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([1230000000000],
      [555000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([4215000000000, 0], [2160000000000,
      9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) fan36Owner4Part0)))))))) (den :=
      9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded36_6 : ExcludedOn (model36.B 6 ++ [step36.q]) 9000000000000 (model36.caps 6)
    (model36.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded36_6
    · exact excluded36_7
    · exact excluded36_8
    · exact excluded36_9
theorem next36 : model36.insert step36 = model37 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded37_1 : ExcludedOn (model37.B 1 ++ [step37.q]) 9000000000000 (model37.caps 1)
    (model37.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_2 : ExcludedOn (model37.B 2 ++ [step37.q]) 9000000000000 (model37.caps 2)
    (model37.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_3 : ExcludedOn (model37.B 3 ++ [step37.q]) 9000000000000 (model37.caps 3)
    (model37.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6840000000000, -9000000000000], [345000000000,
      9000000000000]) (some (3, 0, 5)) (some (4, 0, 5)) (.next ([7320000000000], [1680000000000])
      (some (4, 0, 5)) (some (4, 5, 5)) (.next ([6840000000000], [1785000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) fan37Owner3Part0))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_4 : ExcludedOn (model37.B 4 ++ [step37.q]) 9000000000000 (model37.caps 4)
    (model37.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3090000000000, -9000000000000], [0,
      9000000000000]) (some (5, 0, 6)) (some (5, 1, 6)) (.next ([5820000000000], [660000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([4320000000000, -9000000000000], [555000000000,
      9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([4155000000000], [720000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([3495000000000], [660000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([5025000000000, -9000000000000], [2160000000000, 9000000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([4215000000000, 0], [2160000000000, 9000000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1785000000000], [1095000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([4215000000000], [2970000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      fan37Owner4Part0)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_5 : ExcludedOn (model37.B 5 ++ [step37.q]) 9000000000000 (model37.caps 5)
    (model37.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7185000000000], [1815000000000]) (some (4, 0,
      2)) (some (4, 1, 2)) (.next ([4830000000000], [1785000000000]) (some (4, 1, 2)) (some (4, 1,
      2)) (.next ([4830000000000, 0], [2160000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1,
      2)) (.next ([4455000000000, -9000000000000], [2160000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([5025000000000, -9000000000000], [3975000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 3)) (.next ([3015000000000], [4170000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([570000000000], [1815000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([0], [4830000000000]) (some (0, 1, 3)) (some (0, 1, 4)) (.next ([-1815000000000],
      [9000000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1785000000000], [6615000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2160000000000, -9000000000000], [6990000000000,
      9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2160000000000, -9000000000000],
      [6615000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-3975000000000, -9000000000000],
      [9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4170000000000], [7185000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1815000000000], [2385000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2,
      4))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded37_6 : ExcludedOn (model37.B 6 ++ [step37.q]) 9000000000000 (model37.caps 6)
    (model37.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked37 : StepValid model37 9000000000000 step37 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded37_1
    · exact excluded37_2
    · exact excluded37_3
    · exact excluded37_4
    · exact excluded37_5
    · exact excluded37_6
    · exact excluded37_7
    · exact excluded37_8
    · exact excluded37_9
theorem next37 : model37.insert step37 = model38 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded38_0 : ExcludedOn (model38.B 0 ++ [step38.q]) 9000000000000 (model38.caps 0)
    (model38.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_5 : ExcludedOn (model38.B 5 ++ [step38.q]) 9000000000000 (model38.caps 5)
    (model38.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_6 : ExcludedOn (model38.B 6 ++ [step38.q]) 9000000000000 (model38.caps 6)
    (model38.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2283000000000], [105000000000]) (some (7, 3, 5))
      (some (7, 3, 8)) (.next ([3645000000000], [720000000000]) (some (7, 3, 8)) (some (7, 3, 8))
      (.next ([3795000000000], [855000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next
      ([5760000000000], [1650000000000, 9000000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next
      ([5760000000000], [1875000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([4875000000000],
      [1605000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([5625000000000], [1935000000000,
      9000000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([648000000000], [240000000000])
      (some (7, 3, 8)) (some (7, 3, 8)) (.next ([5625000000000], [2160000000000]) (some (7, 3, 8))
      (some (7, 3, 8)) (.next ([2010000000000], [855000000000]) (some (7, 3, 8)) (some (7, 3, 8))
      (.next ([1362000000000], [615000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next
      ([2160000000000], [990000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([1512000000000],
      [750000000000]) (some (7, 3, 8)) (some (7, 3, 8)) fan38Owner6Part1)))))))))))))) (den :=
      9000000000000)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked38 : StepValid model38 9000000000000 step38 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded38_0
    · exact (hj rfl).elim
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

theorem excluded39_1 : ExcludedOn (model39.B 1 ++ [step39.q]) 9000000000000 (model39.caps 1)
    (model39.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6615000000000, 0], [2160000000000,
      9000000000000]) (some (3, 1, 1)) (some (3, 1, 2)) (.next ([3240000000000], [2385000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([4230000000000], [5625000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([1080000000000, -9000000000000], [2385000000000, 0]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([0, 0], [2160000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([-2160000000000, -9000000000000], [8775000000000, 9000000000000]) (some (3, 1, 0))
      (some (3, 1, 0)) (.next ([-2385000000000], [5625000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-5625000000000], [9855000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-2385000000000, 0], [3465000000000, -9000000000000]) (some (1, 1, 0)) (some (1, 1, 0))
      (.terminal (some (1, 1, 0)) (some (1, 1, 3)) (some (1, 1, 3))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded39_2 : ExcludedOn (model39.B 2 ++ [step39.q]) 9000000000000 (model39.caps 2)
    (model39.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6840000000000, -9000000000000], [2160000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2385000000000], [3375000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1080000000000, -9000000000000], [2385000000000, 0])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([225000000000, -9000000000000], [5535000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [2160000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-2160000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-3375000000000],
      [5760000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2385000000000, 0],
      [3465000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5535000000000,
      -9000000000000], [5760000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded39_3 : ExcludedOn (model39.B 3 ++ [step39.q]) 9000000000000 (model39.caps 3)
    (model39.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_4 : ExcludedOn (model39.B 4 ++ [step39.q]) 9000000000000 (model39.caps 4)
    (model39.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_5 : ExcludedOn (model39.B 5 ++ [step39.q]) 9000000000000 (model39.caps 5)
    (model39.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_6 : ExcludedOn (model39.B 6 ++ [step39.q]) 9000000000000 (model39.caps 6)
    (model39.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_7 : ExcludedOn (model39.B 7 ++ [step39.q]) 9000000000000 (model39.caps 7)
    (model39.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_8 : ExcludedOn (model39.B 8 ++ [step39.q]) 9000000000000 (model39.caps 8)
    (model39.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_9 : ExcludedOn (model39.B 9 ++ [step39.q]) 9000000000000 (model39.caps 9)
    (model39.ord 9) 0 1 100 := by
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
    · exact (hj rfl).elim
    · exact excluded39_1
    · exact excluded39_2
    · exact excluded39_3
    · exact excluded39_4
    · exact excluded39_5
    · exact excluded39_6
    · exact excluded39_7
    · exact excluded39_8
    · exact excluded39_9
theorem next39 : model39.insert step39 = model40 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint240000250000
end ConwaySoifer.Simplified.Certificates
