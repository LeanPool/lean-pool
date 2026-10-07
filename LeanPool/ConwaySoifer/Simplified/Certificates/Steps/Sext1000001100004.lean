/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext100000110000
import Mathlib.Tactic.FinCases

/-!
# Sext 100000 110000 4

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
namespace Sext100000110000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner2Part0 : FanWitness := (.next ([3975000000000], [375000000000]) (some (0, 1, 5)) (some
    (0, 1, 5)) (.next ([5250000000000], [900000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
    ([5745000000000], [4530000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([4845000000000],
    [4530000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([1620000000000, 0], [3225000000000,
    -9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([1800000000000, 9000000000000],
    [3975000000000, -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([1620000000000],
    [4125000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([870000000000], [4155000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([900000000000], [4875000000000]) (some (0, 2, 3))
    (some (0, 5, 3)) (.next ([900000000000, 9000000000000], [6150000000000, 0]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([0, 9000000000000], [6150000000000, 0]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([0], [900000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-375000000000],
    [5250000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next ([-375000000000], [4350000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-900000000000], [6150000000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.next ([-4530000000000], [10275000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-4530000000000], [9375000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-3225000000000, 9000000000000], [4845000000000, -9000000000000]) (some (0, 5, 4)) (some (0, 5,
    4)) (.next ([-3975000000000, 9000000000000], [5775000000000, 0]) (some (0, 5, 4)) (some (0, 5,
    4)) (.next ([-4125000000000], [5745000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-4155000000000], [5025000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-4875000000000],
    [5775000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-6150000000000, 0], [7050000000000,
    9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-6150000000000, 0], [6150000000000,
    9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5, 4)) (some (0, 5, 0))
    (some (0, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner1Part0 : FanWitness := (.next ([3750000000000], [1200000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([2850000000000, -9000000000000], [1200000000000, 0]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([3255000000000], [1620000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([6150000000000], [3600000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([5730000000000], [3525000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2355000000000,
    -9000000000000], [1620000000000, 0]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([900000000000,
    9000000000000], [900000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([1350000000000], [5100000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([1350000000000], [6000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([450000000000,
    -9000000000000], [6900000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0],
    [900000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-300000000000,
    9000000000000], [4950000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next ([-720000000000,
    9000000000000], [4875000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-75000000000],
    [495000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-1200000000000], [4950000000000])
    (some (0, 5, 4)) (some (1, 5, 4)) (.next ([-1200000000000, 0], [4050000000000, -9000000000000])
    (some (1, 5, 4)) none (.next ([-1620000000000], [4875000000000]) none none (.next
    ([-3600000000000], [9750000000000]) none none (.next ([-3525000000000], [9255000000000]) none
    none (.next ([-1620000000000, 0], [3975000000000, -9000000000000]) none none (.next
    ([-900000000000, -9000000000000], [1800000000000, 18000000000000]) none none (.next
    ([-5100000000000, 9000000000000], [6450000000000, -9000000000000]) (some (5, 5, 0)) (some (5, 5,
    0)) (.next ([-6000000000000], [7350000000000]) (some (5, 2, 0)) (some (5, 2, 0)) (.next
    ([-6900000000000, -9000000000000], [7350000000000, 0]) (some (5, 2, 0)) (some (5, 2, 0))
    (.terminal (some (5, 2, 0)) (some (5, 2, 0)) (some (5, 2, 0)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan36Owner2Part0 : FanWitness := (.next ([3975000000000], [375000000000]) (some (0, 5, 3)) (some
    (0, 5, 3)) (.next ([5250000000000], [900000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([1950000000000], [375000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([5775000000000,
    9000000000000], [2325000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([1950000000000], [1275000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([4875000000000],
    [3225000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([1650000000000], [2325000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([1800000000000, 9000000000000], [3975000000000,
    -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([900000000000], [4875000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([900000000000, 9000000000000], [6150000000000, 0])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([0, 9000000000000], [6150000000000, 0]) (some (0, 2,
    3)) (some (0, 2, 3)) (.next ([0], [900000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([-375000000000], [5250000000000]) (some (0, 2, 3)) (some (0, 2, 4)) (.next ([-375000000000],
    [4350000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-900000000000], [6150000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-375000000000], [2325000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([-2325000000000, 9000000000000], [8100000000000, 0]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([-1275000000000], [3225000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([-3225000000000], [8100000000000]) (some (0, 2, 4)) (some (5, 2, 4)) (.next
    ([-2325000000000], [3975000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-3975000000000,
    9000000000000], [5775000000000, 0]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-4875000000000],
    [5775000000000]) (some (5, 2, 4)) (some (5, 3, 4)) (.next ([-6150000000000, 0], [7050000000000,
    9000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-6150000000000, 0], [6150000000000,
    9000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.terminal (some (5, 3, 4)) (some (5, 3, 0))
    (some (5, 3, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner3Part0 : FanWitness := (.next ([1500000000000], [900000000000]) (some (4, 0, 1)) (some
    (4, 0, 1)) (.next ([4125000000000], [2925000000000]) (some (4, 0, 1)) (some (4, 0, 2)) (.next
    ([4500000000000, 9000000000000], [3600000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0,
    2)) (.next ([3600000000000], [4500000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
    ([1950000000000], [2550000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([1500000000000,
    9000000000000], [4125000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 5, 2)) (.next
    ([525000000000], [2475000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([900000000000,
    9000000000000], [6150000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([600000000000],
    [5025000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([0, 9000000000000], [3225000000000,
    -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([0], [6150000000000]) (some (4, 5,
    2)) (some (4, 5, 3)) (.next ([-375000000000], [4875000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-525000000000], [5550000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-900000000000], [4125000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-900000000000],
    [2400000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2925000000000], [7050000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3600000000000, 9000000000000], [8100000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4500000000000], [8100000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-2550000000000], [4500000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-4125000000000, 9000000000000], [5625000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-2475000000000], [3000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-6150000000000, 0], [7050000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-5025000000000], [5625000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3225000000000,
    9000000000000], [3225000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1, 3))
    (some (0, 1, 3)) (some (0, 1, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan38Owner3Part0 : FanWitness := (.next ([4125000000000], [2925000000000]) (some (4, 0, 5))
    (some (4, 0, 5)) (.next ([2850000000000], [5400000000000]) (some (4, 0, 5)) (some (4, 0, 5))
    (.next ([1650000000000], [4125000000000]) (some (4, 0, 5)) (some (4, 5, 5)) (.next
    ([1500000000000, 9000000000000], [4125000000000, -9000000000000]) (some (4, 5, 2)) (some (4, 5,
    2)) (.next ([1650000000000, 9000000000000], [7350000000000, -9000000000000]) (some (4, 5, 2))
    (some (4, 5, 2)) (.next ([900000000000, 9000000000000], [6150000000000]) (some (4, 5, 2)) (some
    (4, 5, 2)) (.next ([600000000000], [5025000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
    ([750000000000], [8250000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([150000000000],
    [3225000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([0, 9000000000000], [3225000000000,
    -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([0], [6150000000000]) (some (4, 5,
    2)) (some (4, 5, 3)) (.next ([-525000000000], [5550000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-900000000000], [4125000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-900000000000], [2400000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2925000000000],
    [7050000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-5400000000000], [8250000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4125000000000], [5775000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-4125000000000, 9000000000000], [5625000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-7350000000000, 9000000000000], [9000000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-6150000000000, 0], [7050000000000, 9000000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-5025000000000], [5625000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-8250000000000], [9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-3225000000000], [3375000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3225000000000,
    9000000000000], [3225000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3))
    (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan38Owner5Part0 : FanWitness := (.next ([75000000000], [75000000000]) (some (5, 1, 2)) (some
    (5, 1, 2)) (.next ([75000000000, 9000000000000], [300000000000, -9000000000000]) (some (5, 1,
    2)) (some (5, 1, 2)) (.next ([375000000000], [825000000000]) (some (5, 1, 2)) (some (5, 1, 2))
    (.next ([225000000000], [900000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([1200000000000], [6870000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1125000000000],
    [7020000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([900000000000, 9000000000000],
    [7245000000000, 0]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1005000000000], [7995000000000])
    (some (5, 1, 2)) (some (5, 1, 2)) (.next ([150000000000, 9000000000000], [8100000000000,
    -9000000000000]) (some (5, 1, 2)) (some (5, 1, 5)) (.next ([150000000000], [7875000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([75000000000], [7800000000000]) (some (0, 1, 5)) (some
    (0, 1, 5)) (.next ([0, 0], [900000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-750000000000], [9000000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
    ([-75000000000], [150000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-300000000000,
    9000000000000], [375000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-825000000000],
    [1200000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-900000000000], [1125000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-6870000000000], [8070000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-7020000000000], [8145000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-7245000000000, 0], [8145000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-7995000000000], [9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-8100000000000, 9000000000000], [8250000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-7875000000000], [8025000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-7800000000000],
    [7875000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2, 5))
    (some (0, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan39Owner3Part0 : FanWitness := (.next ([5025000000000], [525000000000]) (some (4, 0, 5)) (some
    (4, 0, 5)) (.next ([3225000000000], [900000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
    ([2775000000000], [825000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([1500000000000],
    [900000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([4125000000000], [2925000000000])
    (some (4, 0, 5)) (some (4, 0, 5)) (.next ([1500000000000, 9000000000000], [4125000000000,
    -9000000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([2250000000000], [6375000000000])
    (some (4, 0, 5)) (some (4, 0, 5)) (.next ([900000000000, 9000000000000], [6150000000000]) (some
    (4, 0, 5)) (some (4, 5, 5)) (.next ([600000000000], [5025000000000]) (some (4, 5, 5)) (some (4,
    5, 2)) (.next ([675000000000, 9000000000000], [7725000000000, -9000000000000]) (some (4, 5, 2))
    (some (4, 5, 2)) (.next ([0, 9000000000000], [3225000000000, -9000000000000]) (some (4, 5, 2))
    (some (4, 5, 2)) (.next ([0], [6150000000000]) (some (4, 5, 2)) (some (4, 5, 3)) (.next
    ([-225000000000], [8625000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-525000000000],
    [5550000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-900000000000], [4125000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-825000000000], [3600000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-900000000000], [2400000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-2925000000000], [7050000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-4125000000000, 9000000000000], [5625000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-6375000000000], [8625000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-6150000000000,
    0], [7050000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-5025000000000],
    [5625000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-7725000000000, 9000000000000],
    [8400000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3225000000000, 9000000000000],
    [3225000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3)) (some (0, 5, 3))
    (some (0, 5, 3)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_2 : ExcludedOn (model32.B 2 ++ [step32.q]) 9000000000000 (model32.caps 2)
    (model32.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4875000000000], [375000000000]) (some (0, 0, 5))
      (some (0, 1, 5)) fan32Owner2Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded32_3 : ExcludedOn (model32.B 3 ++ [step32.q]) 9000000000000 (model32.caps 3)
    (model32.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_4 : ExcludedOn (model32.B 4 ++ [step32.q]) 9000000000000 (model32.caps 4)
    (model32.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_5 : ExcludedOn (model32.B 5 ++ [step32.q]) 9000000000000 (model32.caps 5)
    (model32.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_6 : ExcludedOn (model32.B 6 ++ [step32.q]) 9000000000000 (model32.caps 6)
    (model32.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_7 : ExcludedOn (model32.B 7 ++ [step32.q]) 9000000000000 (model32.caps 7)
    (model32.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_8 : ExcludedOn (model32.B 8 ++ [step32.q]) 9000000000000 (model32.caps 8)
    (model32.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_9 : ExcludedOn (model32.B 9 ++ [step32.q]) 9000000000000 (model32.caps 9)
    (model32.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded33_1 : ExcludedOn (model33.B 1 ++ [step33.q]) 9000000000000 (model33.caps 1)
    (model33.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_2 : ExcludedOn (model33.B 2 ++ [step33.q]) 9000000000000 (model33.caps 2)
    (model33.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_3 : ExcludedOn (model33.B 3 ++ [step33.q]) 9000000000000 (model33.caps 3)
    (model33.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_4 : ExcludedOn (model33.B 4 ++ [step33.q]) 9000000000000 (model33.caps 4)
    (model33.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_5 : ExcludedOn (model33.B 5 ++ [step33.q]) 9000000000000 (model33.caps 5)
    (model33.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8205000000000], [795000000000]) (some (5, 0, 5))
      (some (5, 1, 5)) (.next ([8280000000000], [870000000000]) (some (3, 1, 5)) (some (3, 1, 5))
      (.next ([8280000000000, 9000000000000], [1095000000000, -9000000000000]) (some (3, 1, 5))
      (some (3, 1, 5)) (.next ([7380000000000], [1995000000000]) (some (3, 1, 5)) (some (3, 1, 5))
      (.next ([75000000000], [75000000000]) (some (3, 1, 5)) (some (3, 1, 5)) (.next ([75000000000,
      9000000000000], [300000000000, -9000000000000]) (some (3, 1, 5)) (some (4, 1, 5)) (.next ([0,
      9000000000000], [225000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0,
      0], [900000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-795000000000],
      [9000000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-870000000000], [9150000000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1095000000000, 9000000000000], [9375000000000, 0])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1995000000000], [9375000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([-75000000000], [150000000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-300000000000, 9000000000000], [375000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-225000000000, 9000000000000], [225000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5))
      (.terminal (some (0, 2, 5)) (some (0, 5, 5)) (some (0, 2, 5))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1275000000000, 9000000000000], [720000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([1620000000000], [6105000000000,
      -9000000000000]) (some (2, 0, 2)) (some (2, 0, 2)) (.next ([375000000000], [1620000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([900000000000, 9000000000000], [8100000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [900000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-720000000000, 9000000000000],
      [1995000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-6105000000000, 9000000000000],
      [7725000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1620000000000],
      [1995000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-8100000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_7 : ExcludedOn (model33.B 7 ++ [step33.q]) 9000000000000 (model33.caps 7)
    (model33.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_8 : ExcludedOn (model33.B 8 ++ [step33.q]) 9000000000000 (model33.caps 8)
    (model33.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_9 : ExcludedOn (model33.B 9 ++ [step33.q]) 9000000000000 (model33.caps 9)
    (model33.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked33 : StepValid model33 9000000000000 step33 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded33_1
    · exact excluded33_2
    · exact excluded33_3
    · exact excluded33_4
    · exact excluded33_5
    · exact excluded33_6
    · exact excluded33_7
    · exact excluded33_8
    · exact excluded33_9
theorem next33 : model33.insert step33 = model34 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded34_1 : ExcludedOn (model34.B 1 ++ [step34.q]) 9000000000000 (model34.caps 1)
    (model34.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4650000000000, 9000000000000], [300000000000,
      -9000000000000]) (some (0, 5, 2)) (some (0, 5, 3)) (.next ([4155000000000, 9000000000000],
      [720000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([420000000000],
      [75000000000]) (some (0, 5, 3)) (some (0, 5, 3)) fan34Owner1Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0
      1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_3 : ExcludedOn (model34.B 3 ++ [step34.q]) 9000000000000 (model34.caps 3)
    (model34.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_4 : ExcludedOn (model34.B 4 ++ [step34.q]) 9000000000000 (model34.caps 4)
    (model34.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2550000000000, 9000000000000], [450000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([1650000000000], [1350000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1350000000000], [5100000000000, -9000000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([900000000000, 9000000000000], [8100000000000,
      -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [900000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-450000000000, 9000000000000],
      [3000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-1350000000000], [3000000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5100000000000, 9000000000000], [6450000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-8100000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_7 : ExcludedOn (model34.B 7 ++ [step34.q]) 9000000000000 (model34.caps 7)
    (model34.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_8 : ExcludedOn (model34.B 8 ++ [step34.q]) 9000000000000 (model34.caps 8)
    (model34.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_9 : ExcludedOn (model34.B 9 ++ [step34.q]) 9000000000000 (model34.caps 9)
    (model34.ord 9) 0 1 100 := by
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
    · exact (hj rfl).elim
    · exact excluded34_1
    · exact excluded34_2
    · exact excluded34_3
    · exact excluded34_4
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
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_1 : ExcludedOn (model35.B 1 ++ [step35.q]) 9000000000000 (model35.caps 1)
    (model35.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4650000000000, 9000000000000], [300000000000,
      -9000000000000]) (some (5, 1, 2)) (some (5, 1, 5)) (.next ([4155000000000, 9000000000000],
      [720000000000, -9000000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([420000000000],
      [75000000000]) (some (5, 1, 5)) (some (5, 2, 5)) (.next ([3750000000000], [1200000000000])
      (some (5, 2, 5)) (some (5, 2, 5)) (.next ([2850000000000, -9000000000000], [1200000000000, 0])
      (some (5, 2, 5)) (some (5, 2, 5)) (.next ([3255000000000], [1620000000000]) (some (5, 2, 5))
      (some (5, 2, 5)) (.next ([2355000000000, -9000000000000], [1620000000000, 0]) (some (5, 2, 5))
      (some (5, 2, 5)) (.next ([4950000000000], [3900000000000]) (some (5, 2, 5)) (some (5, 2, 5))
      (.next ([4875000000000], [4395000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([900000000000, 9000000000000], [900000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2,
      5)) (.next ([900000000000, 9000000000000], [6750000000000, -9000000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([0], [900000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-300000000000, 9000000000000], [4950000000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-720000000000, 9000000000000], [4875000000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-75000000000], [495000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-1200000000000], [4950000000000]) (some (0, 2, 5)) (some (1, 2, 5)) (.next ([-1200000000000,
      0], [4050000000000, -9000000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next
      ([-1620000000000], [4875000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next ([-1620000000000,
      0], [3975000000000, -9000000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next
      ([-3900000000000], [8850000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next
      ([-4395000000000], [9270000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next ([-900000000000,
      -9000000000000], [1800000000000, 18000000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next
      ([-6750000000000, 9000000000000], [7650000000000, 0]) (some (1, 2, 5)) (some (1, 2, 5))
      (.terminal (some (1, 2, 5)) (some (1, 2, 5)) (some (1, 2, 5))))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_2 : ExcludedOn (model35.B 2 ++ [step35.q]) 9000000000000 (model35.caps 2)
    (model35.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_3 : ExcludedOn (model35.B 3 ++ [step35.q]) 9000000000000 (model35.caps 3)
    (model35.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_4 : ExcludedOn (model35.B 4 ++ [step35.q]) 9000000000000 (model35.caps 4)
    (model35.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_5 : ExcludedOn (model35.B 5 ++ [step35.q]) 9000000000000 (model35.caps 5)
    (model35.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_6 : ExcludedOn (model35.B 6 ++ [step35.q]) 9000000000000 (model35.caps 6)
    (model35.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_8 : ExcludedOn (model35.B 8 ++ [step35.q]) 9000000000000 (model35.caps 8)
    (model35.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_9 : ExcludedOn (model35.B 9 ++ [step35.q]) 9000000000000 (model35.caps 9)
    (model35.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded35_4
    · exact excluded35_5
    · exact excluded35_6
    · exact (hj rfl).elim
    · exact excluded35_8
    · exact excluded35_9
theorem next35 : model35.insert step35 = model36 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded36_0 : ExcludedOn (model36.B 0 ++ [step36.q]) 9000000000000 (model36.caps 0)
    (model36.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_1 : ExcludedOn (model36.B 1 ++ [step36.q]) 9000000000000 (model36.caps 1)
    (model36.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_2 : ExcludedOn (model36.B 2 ++ [step36.q]) 9000000000000 (model36.caps 2)
    (model36.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4875000000000], [375000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) fan36Owner2Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded36_4 : ExcludedOn (model36.B 4 ++ [step36.q]) 9000000000000 (model36.caps 4)
    (model36.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_6 : ExcludedOn (model36.B 6 ++ [step36.q]) 9000000000000 (model36.caps 6)
    (model36.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_7 : ExcludedOn (model36.B 7 ++ [step36.q]) 9000000000000 (model36.caps 7)
    (model36.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_8 : ExcludedOn (model36.B 8 ++ [step36.q]) 9000000000000 (model36.caps 8)
    (model36.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_9 : ExcludedOn (model36.B 9 ++ [step36.q]) 9000000000000 (model36.caps 9)
    (model36.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_1 : ExcludedOn (model37.B 1 ++ [step37.q]) 9000000000000 (model37.caps 1)
    (model37.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_2 : ExcludedOn (model37.B 2 ++ [step37.q]) 9000000000000 (model37.caps 2)
    (model37.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_3 : ExcludedOn (model37.B 3 ++ [step37.q]) 9000000000000 (model37.caps 3)
    (model37.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4500000000000], [375000000000]) (some (3, 0, 1))
      (some (4, 0, 1)) (.next ([5025000000000], [525000000000]) (some (4, 0, 1)) (some (4, 0, 1))
      (.next ([3225000000000], [900000000000]) (some (4, 0, 1)) (some (4, 0, 1))
      fan37Owner3Part0)))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_5 : ExcludedOn (model37.B 5 ++ [step37.q]) 9000000000000 (model37.caps 5)
    (model37.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_6 : ExcludedOn (model37.B 6 ++ [step37.q]) 9000000000000 (model37.caps 6)
    (model37.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_7 : ExcludedOn (model37.B 7 ++ [step37.q]) 9000000000000 (model37.caps 7)
    (model37.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_8 : ExcludedOn (model37.B 8 ++ [step37.q]) 9000000000000 (model37.caps 8)
    (model37.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded37_0
    · exact excluded37_1
    · exact excluded37_2
    · exact excluded37_3
    · exact (hj rfl).elim
    · exact excluded37_5
    · exact excluded37_6
    · exact excluded37_7
    · exact excluded37_8
    · exact excluded37_9
theorem next37 : model37.insert step37 = model38 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded38_1 : ExcludedOn (model38.B 1 ++ [step38.q]) 9000000000000 (model38.caps 1)
    (model38.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_2 : ExcludedOn (model38.B 2 ++ [step38.q]) 9000000000000 (model38.caps 2)
    (model38.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_3 : ExcludedOn (model38.B 3 ++ [step38.q]) 9000000000000 (model38.caps 3)
    (model38.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5025000000000], [525000000000]) (some (3, 0, 5))
      (some (4, 0, 5)) (.next ([3225000000000], [900000000000]) (some (4, 0, 5)) (some (4, 0, 5))
      (.next ([1500000000000], [900000000000]) (some (4, 0, 5)) (some (4, 0, 5))
      fan38Owner3Part0)))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded38_4 : ExcludedOn (model38.B 4 ++ [step38.q]) 9000000000000 (model38.caps 4)
    (model38.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4500000000000], [900000000000]) (some (3, 0, 4))
      (some (3, 1, 4)) (.next ([5400000000000], [1650000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([2100000000000], [6150000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([900000000000], [2850000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([900000000000,
      9000000000000], [6150000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([900000000000,
      9000000000000], [7350000000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0,
      9000000000000], [4500000000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([0], [6150000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([-900000000000],
      [5400000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-1650000000000], [7050000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-6150000000000], [8250000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-2850000000000], [3750000000000]) (some (0, 1, 4)) (some (0, 4, 4))
      (.next ([-6150000000000], [7050000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([-7350000000000, 9000000000000], [8250000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([-4500000000000, 9000000000000], [4500000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 3)) (some (0, 4, 3))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded38_5 : ExcludedOn (model38.B 5 ++ [step38.q]) 9000000000000 (model38.caps 5)
    (model38.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (1) (2) (200) (.witnessedFan (.next ([8250000000000],
      [750000000000]) (some (5, 0, 2)) (some (5, 1, 2)) (.next ([75000000000], [75000000000]) (some
      (5, 1, 2)) (some (5, 1, 2)) (.next ([375000000000], [825000000000]) (some (5, 1, 2)) (some (5,
      1, 2)) (.next ([225000000000], [900000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([1200000000000], [6870000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1125000000000],
      [7020000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([900000000000, 9000000000000],
      [7245000000000, 0]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([150000000000, 9000000000000],
      [8100000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1, 5)) (.next ([75000000000],
      [7800000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0, 0], [900000000000,
      9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-750000000000], [9000000000000])
      (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-75000000000], [150000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([-825000000000], [1200000000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-900000000000], [1125000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-6870000000000], [8070000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-7020000000000], [8145000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-7245000000000,
      0], [8145000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-8100000000000,
      9000000000000], [8250000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-7800000000000], [7875000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2,
      5)) (some (0, 2, 5)) (some (0, 2, 5))))))))))))))))))))))) (.witnessedFan (.next
      ([8250000000000], [750000000000]) (some (5, 0, 2)) (some (5, 1, 2)) fan38Owner5Part0))) (den
      := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded38_6 : ExcludedOn (model38.B 6 ++ [step38.q]) 9000000000000 (model38.caps 6)
    (model38.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_7 : ExcludedOn (model38.B 7 ++ [step38.q]) 9000000000000 (model38.caps 7)
    (model38.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_8 : ExcludedOn (model38.B 8 ++ [step38.q]) 9000000000000 (model38.caps 8)
    (model38.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded39_1 : ExcludedOn (model39.B 1 ++ [step39.q]) 9000000000000 (model39.caps 1)
    (model39.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_2 : ExcludedOn (model39.B 2 ++ [step39.q]) 9000000000000 (model39.caps 2)
    (model39.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4875000000000], [375000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([3975000000000], [375000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([5250000000000], [900000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([3000000000000], [525000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2625000000000],
      [4875000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([1800000000000, 9000000000000],
      [3975000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([900000000000],
      [4875000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([1275000000000, 9000000000000],
      [7500000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([900000000000,
      9000000000000], [6150000000000, 0]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([375000000000],
      [8400000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0, 9000000000000], [6150000000000,
      0]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0], [900000000000]) (some (0, 5, 3)) (some (0,
      5, 3)) (.next ([-375000000000], [5250000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next
      ([-375000000000], [4350000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-900000000000],
      [6150000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-525000000000], [3525000000000])
      (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-4875000000000], [7500000000000]) (some (0, 5, 4))
      (some (0, 5, 4)) (.next ([-3975000000000, 9000000000000], [5775000000000, 0]) (some (0, 5, 4))
      (some (0, 5, 4)) (.next ([-4875000000000], [5775000000000]) (some (0, 5, 4)) (some (5, 5, 4))
      (.next ([-7500000000000, 9000000000000], [8775000000000, 0]) (some (5, 5, 4)) (some (5, 5, 4))
      (.next ([-6150000000000, 0], [7050000000000, 9000000000000]) (some (5, 3, 4)) (some (5, 3, 4))
      (.next ([-8400000000000], [8775000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next
      ([-6150000000000, 0], [6150000000000, 9000000000000]) (some (5, 3, 4)) (some (5, 3, 4))
      (.terminal (some (5, 3, 4)) (some (5, 3, 0)) (some (5, 3, 4))))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded39_3 : ExcludedOn (model39.B 3 ++ [step39.q]) 9000000000000 (model39.caps 3)
    (model39.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8400000000000], [225000000000]) (some (3, 0, 5))
      (some (4, 0, 5)) fan39Owner3Part0)) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded39_4 : ExcludedOn (model39.B 4 ++ [step39.q]) 9000000000000 (model39.caps 4)
    (model39.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8625000000000], [600000000000]) (some (3, 0, 4))
      (some (3, 1, 4)) (.next ([4500000000000], [900000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([5400000000000], [1650000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([2475000000000], [6750000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([900000000000,
      9000000000000], [6150000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([300000000000],
      [3825000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([300000000000, 9000000000000],
      [8325000000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0, 9000000000000],
      [4500000000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0],
      [6150000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([-600000000000], [9225000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-900000000000], [5400000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-1650000000000], [7050000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-6750000000000], [9225000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-6150000000000], [7050000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 4, 4)) (.next
      ([-3825000000000], [4125000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.next ([-8325000000000,
      9000000000000], [8625000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4500000000000,
      9000000000000], [4500000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.terminal (some (0, 4, 2))
      (some (0, 4, 3)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded39_5 : ExcludedOn (model39.B 5 ++ [step39.q]) 9000000000000 (model39.caps 5)
    (model39.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_6 : ExcludedOn (model39.B 6 ++ [step39.q]) 9000000000000 (model39.caps 6)
    (model39.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_7 : ExcludedOn (model39.B 7 ++ [step39.q]) 9000000000000 (model39.caps 7)
    (model39.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_8 : ExcludedOn (model39.B 8 ++ [step39.q]) 9000000000000 (model39.caps 8)
    (model39.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

end Sext100000110000
end ConwaySoifer.Simplified.Certificates
