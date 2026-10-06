/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown120000130000
import Mathlib.Tactic.FinCases

/-!
# Aown 120000 130000 2

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
namespace Aown120000130000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part0 : FanWitness := (.next ([-1138200000000, -2610000000000], [7751400000000,
    5220000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([-1213200000000, -2610000000000],
    [7682400000000, 5220000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([-69000000000],
    [429000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([-313200000000, -2610000000000],
    [1706400000000, 5220000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next ([-1451400000000,
    -5220000000000], [7438200000000, 2610000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next
    ([-1526400000000, -5220000000000], [7369200000000, 2610000000000]) (some (8, 3, 4)) (some (8, 3,
    4)) (.next ([-1706400000000, -5220000000000], [6688200000000, 2610000000000]) (some (8, 3, 4))
    (some (8, 3, 4)) (.next ([-69000000000], [144000000000]) (some (8, 3, 4)) (some (8, 3, 4))
    (.next ([-313200000000, -2610000000000], [626400000000, 5220000000000]) (some (8, 3, 4)) (some
    (8, 3, 5)) (.next ([-766800000000, 2610000000000], [1393200000000, 2610000000000]) (some (8, 3,
    5)) (some (8, 3, 5)) (.next ([-750000000000], [1290000000000]) (some (8, 3, 5)) (some (8, 3, 5))
    (.next ([-6375000000000], [10155000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next
    ([-5625000000000], [8865000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-6375000000000],
    [9870000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-6306000000000], [9726000000000])
    (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-3256800000000, 2610000000000], [4633200000000,
    2610000000000]) (some (8, 3, 5)) (some (8, 3, 8)) (.next ([-2943600000000, 5220000000000],
    [4006800000000, -2610000000000]) (some (1, 3, 8)) (some (1, 3, 8)) (.next ([-750000000000],
    [1005000000000]) (some (1, 3, 8)) (some (1, 3, 8)) (.next ([-3883200000000, -2610000000000],
    [4946400000000, 5220000000000]) (some (1, 3, 8)) (some (1, 3, 8)) (.next ([-681000000000],
    [861000000000]) (some (1, 3, 8)) (some (1, 3, 8)) (.next ([-1393200000000, -2610000000000],
    [1706400000000, 5220000000000]) (some (1, 3, 8)) (some (1, 3, 8)) (.next ([-6045000000000],
    [6585000000000]) (some (1, 3, 8)) (some (1, 3, 8)) (.next ([-6045000000000], [6300000000000])
    (some (1, 3, 8)) (some (1, 3, 8)) (.next ([-5976000000000], [6156000000000]) (some (1, 3, 8))
    (some (1, 3, 8)) (.terminal (some (1, 3, 8)) (some (1, 3, 8)) (some (1, 3,
    8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part1 : FanWitness := (.next ([4981800000000, -2610000000000], [1706400000000,
    5220000000000]) (some (8, 1, 3)) (some (8, 1, 3)) (.next ([75000000000], [69000000000]) (some
    (8, 1, 3)) (some (8, 1, 3)) (.next ([313200000000, 2610000000000], [313200000000,
    2610000000000]) (some (8, 1, 3)) (some (8, 1, 3)) (.next ([626400000000, 5220000000000],
    [766800000000, -2610000000000]) (some (8, 1, 3)) (some (8, 2, 3)) (.next ([540000000000],
    [750000000000]) (some (8, 2, 3)) (some (8, 2, 3)) (.next ([3780000000000], [6375000000000])
    (some (8, 2, 3)) (some (8, 2, 3)) (.next ([3240000000000], [5625000000000]) (some (8, 2, 3))
    (some (8, 2, 3)) (.next ([3495000000000], [6375000000000]) (some (8, 2, 3)) (some (8, 2, 3))
    (.next ([3420000000000], [6306000000000]) (some (8, 2, 3)) (some (8, 2, 3)) (.next
    ([1376400000000, 5220000000000], [3256800000000, -2610000000000]) (some (8, 2, 3)) (some (8, 2,
    3)) (.next ([1063200000000, 2610000000000], [2943600000000, -5220000000000]) (some (8, 2, 3))
    (some (8, 2, 3)) (.next ([255000000000], [750000000000]) (some (8, 2, 3)) (some (8, 2, 3))
    (.next ([1063200000000, 2610000000000], [3883200000000, 2610000000000]) (some (8, 2, 3)) (some
    (8, 2, 3)) (.next ([180000000000], [681000000000]) (some (8, 2, 3)) (some (8, 2, 3)) (.next
    ([313200000000, 2610000000000], [1393200000000, 2610000000000]) (some (8, 2, 3)) (some (8, 2,
    3)) (.next ([540000000000], [6045000000000]) (some (8, 2, 3)) (some (8, 2, 3)) (.next
    ([255000000000], [6045000000000]) (some (8, 2, 3)) (some (8, 2, 3)) (.next ([180000000000],
    [5976000000000]) (some (8, 2, 3)) (some (8, 2, 3)) (.next ([0, 0], [939600000000,
    7830000000000]) (some (8, 2, 3)) (some (8, 2, 3)) (.next ([-226800000000, 2610000000000],
    [7438200000000, 2610000000000]) (some (8, 2, 3)) (some (8, 2, 4)) (.next ([-511800000000,
    2610000000000], [7438200000000, 2610000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
    ([-586800000000, 2610000000000], [7369200000000, 2610000000000]) (some (8, 2, 4)) (some (8, 2,
    4)) (.next ([-330000000000], [3570000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
    ([-853200000000, -2610000000000], [7751400000000, 5220000000000]) (some (8, 2, 4)) (some (8, 2,
    4)) fan18Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner4Part0 : FanWitness := (.next ([3450000000000], [750000000000]) (some (3, 1, 5)) (some
    (3, 1, 5)) (.next ([4200000000000, -9000000000000], [1800000000000, 9000000000000]) (some (3, 1,
    5)) (some (3, 1, 5)) (.next ([5430000000000], [3240000000000, -9000000000000]) (some (3, 1, 5))
    (some (3, 1, 5)) (.next ([5430000000000], [4320000000000]) (some (3, 1, 5)) (some (3, 1, 5))
    (.next ([1080000000000, 9000000000000], [1080000000000, 9000000000000]) (some (3, 1, 5)) (some
    (3, 1, 5)) (.next ([4350000000000, -9000000000000], [5400000000000, 9000000000000]) (some (3, 1,
    5)) (some (3, 1, 5)) (.next ([1080000000000], [3090000000000, -9000000000000]) (some (3, 1, 5))
    (some (3, 1, 5)) (.next ([1080000000000], [4170000000000]) (some (3, 1, 5)) (some (4, 1, 5))
    (.next ([360000000000, 9000000000000], [4920000000000, -9000000000000]) (some (4, 1, 5)) (some
    (4, 1, 5)) (.next ([150000000000], [3600000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([0, 0], [1080000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0,
    -9000000000000], [5250000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-150000000000], [4500000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-720000000000],
    [6000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-750000000000], [4200000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1800000000000, -9000000000000], [6000000000000, 0])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3240000000000, 9000000000000], [8670000000000,
    -9000000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-4320000000000], [9750000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1080000000000, -9000000000000], [2160000000000,
    18000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5400000000000, -9000000000000],
    [9750000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3090000000000, 9000000000000],
    [4170000000000, -9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4170000000000],
    [5250000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4920000000000, 9000000000000],
    [5280000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3600000000000], [3750000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 5, 5)) (some (0, 5,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner0Part0 : FanWitness := (.next ([-1138200000000, -2610000000000], [7751400000000,
    5220000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([-1213200000000, -2610000000000],
    [7682400000000, 5220000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([-69000000000],
    [429000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([-313200000000, -2610000000000],
    [1706400000000, 5220000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([-1451400000000,
    -5220000000000], [7438200000000, 2610000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next
    ([-1526400000000, -5220000000000], [7369200000000, 2610000000000]) (some (0, 8, 4)) (some (0, 8,
    4)) (.next ([-1706400000000, -5220000000000], [6688200000000, 2610000000000]) (some (0, 8, 4))
    (some (0, 8, 4)) (.next ([-1110000000000], [3915000000000]) (some (0, 8, 4)) (some (0, 8, 4))
    (.next ([-1395000000000], [4200000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next
    ([-1539000000000], [4275000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([-3240000000000],
    [7695000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([-69000000000], [144000000000]) (some
    (0, 8, 4)) (some (0, 8, 4)) (.next ([-313200000000, -2610000000000], [626400000000,
    5220000000000]) (some (0, 8, 4)) (some (0, 8, 5)) (.next ([-766800000000, 2610000000000],
    [1393200000000, 2610000000000]) (some (0, 8, 5)) (some (1, 8, 5)) (.next ([-4633200000000,
    -2610000000000], [8321400000000, 5220000000000]) (some (1, 8, 5)) (some (1, 8, 5)) (.next
    ([-750000000000], [1290000000000]) (some (1, 8, 5)) (some (1, 8, 5)) (.next ([-4946400000000,
    -5220000000000], [8008200000000, 2610000000000]) (some (1, 8, 5)) (some (1, 8, 5)) (.next
    ([-4633200000000, -2610000000000], [7381800000000, -2610000000000]) (some (1, 8, 5)) (some (1,
    8, 5)) (.next ([-750000000000], [1005000000000]) (some (1, 8, 5)) (some (1, 8, 5)) (.next
    ([-681000000000], [861000000000]) (some (1, 8, 5)) (some (1, 8, 5)) (.next ([-1393200000000,
    -2610000000000], [1706400000000, 5220000000000]) (some (1, 8, 5)) (some (1, 8, 6)) (.next
    ([-6045000000000], [6585000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-6045000000000],
    [6300000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-5976000000000], [6156000000000])
    (some (1, 8, 6)) (some (1, 8, 6)) (.terminal (some (1, 8, 6)) (some (1, 8, 6)) (some (1, 8,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner0Part1 : FanWitness := (.next ([5842800000000, -2610000000000], [1526400000000,
    5220000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([4981800000000, -2610000000000],
    [1706400000000, 5220000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([2805000000000],
    [1110000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([2805000000000], [1395000000000])
    (some (7, 1, 3)) (some (7, 1, 3)) (.next ([2736000000000], [1539000000000]) (some (7, 1, 3))
    (some (7, 1, 3)) (.next ([4455000000000], [3240000000000]) (some (7, 1, 3)) (some (7, 1, 3))
    (.next ([75000000000], [69000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([313200000000,
    2610000000000], [313200000000, 2610000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next
    ([626400000000, 5220000000000], [766800000000, -2610000000000]) (some (7, 1, 3)) (some (7, 2,
    3)) (.next ([3688200000000, 2610000000000], [4633200000000, 2610000000000]) (some (0, 2, 3))
    (some (0, 2, 3)) (.next ([540000000000], [750000000000]) (some (0, 2, 3)) (some (0, 2, 3))
    (.next ([3061800000000, -2610000000000], [4946400000000, 5220000000000]) (some (0, 2, 3)) (some
    (0, 2, 3)) (.next ([2748600000000, -5220000000000], [4633200000000, 2610000000000]) (some (0, 2,
    3)) (some (0, 2, 3)) (.next ([255000000000], [750000000000]) (some (0, 2, 3)) (some (0, 8, 3))
    (.next ([180000000000], [681000000000]) (some (0, 8, 3)) (some (0, 8, 3)) (.next ([313200000000,
    2610000000000], [1393200000000, 2610000000000]) (some (0, 8, 3)) (some (0, 8, 3)) (.next
    ([540000000000], [6045000000000]) (some (0, 8, 3)) (some (0, 8, 3)) (.next ([255000000000],
    [6045000000000]) (some (0, 8, 3)) (some (0, 8, 3)) (.next ([180000000000], [5976000000000])
    (some (0, 8, 3)) (some (0, 8, 3)) (.next ([0, 0], [939600000000, 7830000000000]) (some (0, 8,
    3)) (some (0, 8, 3)) (.next ([-226800000000, 2610000000000], [7438200000000, 2610000000000])
    (some (0, 8, 3)) (some (0, 8, 4)) (.next ([-511800000000, 2610000000000], [7438200000000,
    2610000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([-586800000000, 2610000000000],
    [7369200000000, 2610000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([-853200000000,
    -2610000000000], [7751400000000, 5220000000000]) (some (0, 8, 4)) (some (0, 8, 4))
    fan19Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part0 : FanWitness := (.next ([-1138200000000, -2610000000000], [7751400000000,
    5220000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([-1213200000000, -2610000000000],
    [7682400000000, 5220000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([-69000000000],
    [429000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([-313200000000, -2610000000000],
    [1706400000000, 5220000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([-1451400000000,
    -5220000000000], [7438200000000, 2610000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next
    ([-1526400000000, -5220000000000], [7369200000000, 2610000000000]) (some (0, 8, 4)) (some (0, 8,
    4)) (.next ([-1706400000000, -5220000000000], [6688200000000, 2610000000000]) (some (0, 8, 4))
    (some (0, 8, 4)) (.next ([-69000000000], [144000000000]) (some (0, 8, 4)) (some (0, 8, 4))
    (.next ([-4425000000000], [9000000000000]) (some (0, 8, 4)) (some (0, 8, 5)) (.next
    ([-313200000000, -2610000000000], [626400000000, 5220000000000]) (some (0, 8, 5)) (some (0, 8,
    5)) (.next ([-766800000000, 2610000000000], [1393200000000, 2610000000000]) (some (0, 8, 5))
    (some (1, 8, 5)) (.next ([-750000000000], [1290000000000]) (some (1, 8, 5)) (some (1, 8, 5))
    (.next ([-2415000000000], [4035000000000]) (some (1, 8, 5)) (some (1, 8, 5)) (.next
    ([-5818200000000, -2610000000000], [9626400000000, 5220000000000]) (some (1, 8, 5)) (some (1, 8,
    5)) (.next ([-2700000000000], [4320000000000]) (some (1, 8, 5)) (some (1, 8, 5)) (.next
    ([-2844000000000], [4395000000000]) (some (1, 8, 5)) (some (1, 8, 5)) (.next ([-6131400000000,
    -5220000000000], [9313200000000, 2610000000000]) (some (1, 8, 5)) (some (1, 8, 5)) (.next
    ([-5818200000000, -2610000000000], [8686800000000, -2610000000000]) (some (1, 8, 5)) (some (1,
    8, 5)) (.next ([-750000000000], [1005000000000]) (some (1, 8, 5)) (some (1, 8, 5)) (.next
    ([-681000000000], [861000000000]) (some (1, 8, 5)) (some (1, 8, 5)) (.next ([-3705000000000],
    [4575000000000]) (some (1, 8, 5)) (some (1, 8, 6)) (.next ([-6045000000000], [6585000000000])
    (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-6045000000000], [6300000000000]) (some (1, 8, 6))
    (some (1, 8, 6)) (.next ([-5976000000000], [6156000000000]) (some (1, 8, 6)) (some (1, 8, 6))
    (.terminal (some (1, 8, 6)) (some (1, 8, 6)) (some (1, 8, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part1 : FanWitness := (.next ([5842800000000, -2610000000000], [1526400000000,
    5220000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([4981800000000, -2610000000000],
    [1706400000000, 5220000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([75000000000],
    [69000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([4575000000000], [4425000000000]) (some
    (7, 1, 8)) (some (7, 1, 8)) (.next ([313200000000, 2610000000000], [313200000000,
    2610000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([626400000000, 5220000000000],
    [766800000000, -2610000000000]) (some (7, 1, 8)) (some (7, 2, 8)) (.next ([540000000000],
    [750000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([1620000000000], [2415000000000])
    (some (0, 2, 8)) (some (0, 2, 8)) (.next ([3808200000000, 2610000000000], [5818200000000,
    2610000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([1620000000000], [2700000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([1551000000000], [2844000000000]) (some (0, 2, 3))
    (some (0, 2, 3)) (.next ([3181800000000, -2610000000000], [6131400000000, 5220000000000]) (some
    (0, 2, 3)) (some (0, 2, 3)) (.next ([2868600000000, -5220000000000], [5818200000000,
    2610000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([255000000000], [750000000000]) (some
    (0, 2, 3)) (some (0, 8, 3)) (.next ([180000000000], [681000000000]) (some (0, 8, 3)) (some (0,
    8, 3)) (.next ([870000000000], [3705000000000]) (some (0, 8, 3)) (some (0, 8, 3)) (.next
    ([540000000000], [6045000000000]) (some (0, 8, 3)) (some (0, 8, 3)) (.next ([255000000000],
    [6045000000000]) (some (0, 8, 3)) (some (0, 8, 3)) (.next ([180000000000], [5976000000000])
    (some (0, 8, 3)) (some (0, 8, 3)) (.next ([0, 0], [939600000000, 7830000000000]) (some (0, 8,
    3)) (some (0, 8, 3)) (.next ([-226800000000, 2610000000000], [7438200000000, 2610000000000])
    (some (0, 8, 3)) (some (0, 8, 4)) (.next ([-511800000000, 2610000000000], [7438200000000,
    2610000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([-586800000000, 2610000000000],
    [7369200000000, 2610000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([-853200000000,
    -2610000000000], [7751400000000, 5220000000000]) (some (0, 8, 4)) (some (0, 8, 4))
    fan20Owner0Part0))))))))))))))))))))))))

theorem excluded16_0 : ExcludedOn (model16.B 0 ++ [step16.q]) 9000000000000 (model16.caps 0)
    (model16.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_1 : ExcludedOn (model16.B 1 ++ [step16.q]) 9000000000000 (model16.caps 1)
    (model16.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_2 : ExcludedOn (model16.B 2 ++ [step16.q]) 9000000000000 (model16.caps 2)
    (model16.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_3 : ExcludedOn (model16.B 3 ++ [step16.q]) 9000000000000 (model16.caps 3)
    (model16.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_8 : ExcludedOn (model16.B 8 ++ [step16.q]) 9000000000000 (model16.caps 8)
    (model16.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5595000000000, -9000000000000], [1080000000000,
      9000000000000]) (some (0, 0, 3)) (some (0, 1, 3)) (.next ([4830000000000], [5250000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([3750000000000, -9000000000000], [5250000000000, 0])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1425000000000], [3405000000000]) (some (0, 1, 3))
      (some (0, 3, 3)) (.next ([0, 0], [1080000000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3,
      2)) (.next ([-1080000000000, -9000000000000], [6675000000000, 0]) (some (0, 3, 2)) (some (0,
      3, 2)) (.next ([-5250000000000], [10080000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next
      ([-5250000000000, 0], [9000000000000, -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-3405000000000], [4830000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_1 : ExcludedOn (model17.B 1 ++ [step17.q]) 9000000000000 (model17.caps 1)
    (model17.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_2 : ExcludedOn (model17.B 2 ++ [step17.q]) 9000000000000 (model17.caps 2)
    (model17.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_3 : ExcludedOn (model17.B 3 ++ [step17.q]) 9000000000000 (model17.caps 3)
    (model17.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_5 : ExcludedOn (model17.B 5 ++ [step17.q]) 9000000000000 (model17.caps 5)
    (model17.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6000000000000, 0], [2640000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([6000000000000], [3720000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([4920000000000, -9000000000000], [4800000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [1080000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-2640000000000, 9000000000000],
      [8640000000000, -9000000000000]) (some (3, 1, 3)) (some (3, 2, 3)) (.next ([-3720000000000],
      [9720000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-4800000000000, -9000000000000],
      [9720000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2, 3)) (some (0, 2,
      3)) (some (0, 2, 3))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded17_6 : ExcludedOn (model17.B 6 ++ [step17.q]) 9000000000000 (model17.caps 6)
    (model17.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_7 : ExcludedOn (model17.B 7 ++ [step17.q]) 9000000000000 (model17.caps 7)
    (model17.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_8 : ExcludedOn (model17.B 8 ++ [step17.q]) 9000000000000 (model17.caps 8)
    (model17.ord 8) 0 1 100 := by
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
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7211400000000, 5220000000000], [226800000000,
      -2610000000000]) (some (8, 1, 3)) (some (8, 1, 3)) (.next ([6926400000000, 5220000000000],
      [511800000000, -2610000000000]) (some (8, 1, 3)) (some (8, 1, 3)) (.next ([6782400000000,
      5220000000000], [586800000000, -2610000000000]) (some (8, 1, 3)) (some (8, 1, 3)) (.next
      ([3240000000000], [330000000000]) (some (8, 1, 3)) (some (8, 1, 3)) (.next ([6898200000000,
      2610000000000], [853200000000, 2610000000000]) (some (8, 1, 3)) (some (8, 1, 3)) (.next
      ([6613200000000, 2610000000000], [1138200000000, 2610000000000]) (some (8, 1, 3)) (some (8, 1,
      3)) (.next ([6469200000000, 2610000000000], [1213200000000, 2610000000000]) (some (8, 1, 3))
      (some (8, 1, 3)) (.next ([360000000000], [69000000000]) (some (8, 1, 3)) (some (8, 1, 3))
      (.next ([1393200000000, 2610000000000], [313200000000, 2610000000000]) (some (8, 1, 3)) (some
      (8, 1, 3)) (.next ([5986800000000, -2610000000000], [1451400000000, 5220000000000]) (some (8,
      1, 3)) (some (8, 1, 3)) (.next ([5842800000000, -2610000000000], [1526400000000,
      5220000000000]) (some (8, 1, 3)) (some (8, 1, 3)) fan18Owner0Part1)))))))))))) (den :=
      9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_1 : ExcludedOn (model18.B 1 ++ [step18.q]) 9000000000000 (model18.caps 1)
    (model18.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_2 : ExcludedOn (model18.B 2 ++ [step18.q]) 9000000000000 (model18.caps 2)
    (model18.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_4 : ExcludedOn (model18.B 4 ++ [step18.q]) 9000000000000 (model18.caps 4)
    (model18.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5250000000000, 0], [0, 9000000000000]) (some (5,
      0, 5)) (some (5, 1, 5)) (.next ([4350000000000], [150000000000]) (some (5, 1, 5)) (some (5, 1,
      5)) (.next ([5280000000000], [720000000000]) (some (3, 1, 5)) (some (3, 1, 5))
      fan18Owner4Part0)))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_8 : ExcludedOn (model18.B 8 ++ [step18.q]) 9000000000000 (model18.caps 8)
    (model18.ord 8) 0 1 100 := by
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7211400000000, 5220000000000], [226800000000,
      -2610000000000]) (some (6, 1, 8)) (some (7, 1, 8)) (.next ([6926400000000, 5220000000000],
      [511800000000, -2610000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([6782400000000,
      5220000000000], [586800000000, -2610000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next
      ([6898200000000, 2610000000000], [853200000000, 2610000000000]) (some (7, 1, 8)) (some (7, 1,
      8)) (.next ([6613200000000, 2610000000000], [1138200000000, 2610000000000]) (some (7, 1, 8))
      (some (7, 1, 8)) (.next ([6469200000000, 2610000000000], [1213200000000, 2610000000000]) (some
      (7, 1, 8)) (some (7, 1, 8)) (.next ([360000000000], [69000000000]) (some (7, 1, 8)) (some (7,
      1, 8)) (.next ([1393200000000, 2610000000000], [313200000000, 2610000000000]) (some (7, 1, 8))
      (some (7, 1, 8)) (.next ([5986800000000, -2610000000000], [1451400000000, 5220000000000])
      (some (7, 1, 8)) (some (7, 1, 8)) fan19Owner0Part1)))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_1 : ExcludedOn (model19.B 1 ++ [step19.q]) 9000000000000 (model19.caps 1)
    (model19.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1080000000000, 9000000000000], [1080000000000,
      9000000000000]) (some (2, 3, 1)) (some (2, 3, 2)) (.next ([1305000000000], [2295000000000,
      -9000000000000]) (some (2, 3, 2)) (some (2, 3, 2)) (.next ([1080000000000, 9000000000000],
      [3600000000000, -9000000000000]) (some (2, 3, 2)) (some (2, 3, 2)) (.next ([1305000000000],
      [8055000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([225000000000, -9000000000000],
      [4455000000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0], [5760000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-1080000000000, -9000000000000],
      [2160000000000, 18000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next ([-2295000000000,
      9000000000000], [3600000000000, -9000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next
      ([-3600000000000, 9000000000000], [4680000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-8055000000000], [9360000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-4455000000000,
      -9000000000000], [4680000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 2)) (some (3, 1, 2))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_2 : ExcludedOn (model19.B 2 ++ [step19.q]) 9000000000000 (model19.caps 2)
    (model19.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_3 : ExcludedOn (model19.B 3 ++ [step19.q]) 9000000000000 (model19.caps 3)
    (model19.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_4 : ExcludedOn (model19.B 4 ++ [step19.q]) 9000000000000 (model19.caps 4)
    (model19.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_5 : ExcludedOn (model19.B 5 ++ [step19.q]) 9000000000000 (model19.caps 5)
    (model19.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded19_3
    · exact excluded19_4
    · exact excluded19_5
    · exact (hj rfl).elim
    · exact excluded19_7
    · exact excluded19_8
    · exact excluded19_9
theorem next19 : model19.insert step19 = model20 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded20_0 : ExcludedOn (model20.B 0 ++ [step20.q]) 9000000000000 (model20.caps 0)
    (model20.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7211400000000, 5220000000000], [226800000000,
      -2610000000000]) (some (6, 1, 8)) (some (7, 1, 8)) (.next ([6926400000000, 5220000000000],
      [511800000000, -2610000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([6782400000000,
      5220000000000], [586800000000, -2610000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next
      ([6898200000000, 2610000000000], [853200000000, 2610000000000]) (some (7, 1, 8)) (some (7, 1,
      8)) (.next ([6613200000000, 2610000000000], [1138200000000, 2610000000000]) (some (7, 1, 8))
      (some (7, 1, 8)) (.next ([6469200000000, 2610000000000], [1213200000000, 2610000000000]) (some
      (7, 1, 8)) (some (7, 1, 8)) (.next ([360000000000], [69000000000]) (some (7, 1, 8)) (some (7,
      1, 8)) (.next ([1393200000000, 2610000000000], [313200000000, 2610000000000]) (some (7, 1, 8))
      (some (7, 1, 8)) (.next ([5986800000000, -2610000000000], [1451400000000, 5220000000000])
      (some (7, 1, 8)) (some (7, 1, 8)) fan20Owner0Part1)))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3495000000000, 0], [1080000000000,
      9000000000000]) none none (.next ([1080000000000, 9000000000000], [1080000000000,
      9000000000000]) (some (2, 3, 2)) (some (2, 3, 2)) (.next ([1080000000000, 9000000000000],
      [3600000000000, -9000000000000]) (some (2, 3, 2)) (some (2, 3, 2)) (.next ([0],
      [5760000000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-1080000000000,
      -9000000000000], [4575000000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next
      ([-1080000000000, -9000000000000], [2160000000000, 18000000000000]) (some (0, 3, 2)) (some (3,
      3, 2)) (.next ([-3600000000000, 9000000000000], [4680000000000, 0]) (some (3, 3, 2)) (some (3,
      3, 2)) (.terminal (some (3, 3, 2)) none none))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_2 : ExcludedOn (model20.B 2 ++ [step20.q]) 9000000000000 (model20.caps 2)
    (model20.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_3 : ExcludedOn (model20.B 3 ++ [step20.q]) 9000000000000 (model20.caps 3)
    (model20.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_4 : ExcludedOn (model20.B 4 ++ [step20.q]) 9000000000000 (model20.caps 4)
    (model20.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_5 : ExcludedOn (model20.B 5 ++ [step20.q]) 9000000000000 (model20.caps 5)
    (model20.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_7 : ExcludedOn (model20.B 7 ++ [step20.q]) 9000000000000 (model20.caps 7)
    (model20.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_8 : ExcludedOn (model20.B 8 ++ [step20.q]) 9000000000000 (model20.caps 8)
    (model20.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded20_3
    · exact excluded20_4
    · exact excluded20_5
    · exact (hj rfl).elim
    · exact excluded20_7
    · exact excluded20_8
    · exact excluded20_9
theorem next20 : model20.insert step20 = model21 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded21_0 : ExcludedOn (model21.B 0 ++ [step21.q]) 9000000000000 (model21.caps 0)
    (model21.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_1 : ExcludedOn (model21.B 1 ++ [step21.q]) 9000000000000 (model21.caps 1)
    (model21.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_2 : ExcludedOn (model21.B 2 ++ [step21.q]) 9000000000000 (model21.caps 2)
    (model21.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_3 : ExcludedOn (model21.B 3 ++ [step21.q]) 9000000000000 (model21.caps 3)
    (model21.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_4 : ExcludedOn (model21.B 4 ++ [step21.q]) 9000000000000 (model21.caps 4)
    (model21.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5250000000000, 0], [0, 9000000000000]) (some (3,
      0, 2)) (some (3, 1, 2)) (.next ([5280000000000], [720000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([3450000000000], [750000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([3945000000000], [1305000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([4200000000000,
      -9000000000000], [1800000000000, 9000000000000]) (some (3, 1, 2)) (some (5, 1, 2)) (.next
      ([1785000000000, -9000000000000], [1080000000000, 9000000000000]) (some (5, 1, 2)) (some (5,
      1, 2)) (.next ([1080000000000, 9000000000000], [1080000000000, 9000000000000]) (some (5, 1,
      2)) (some (5, 1, 2)) (.next ([2145000000000], [6000000000000]) (some (5, 1, 2)) (some (5, 1,
      2)) (.next ([1080000000000], [4170000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([360000000000, 9000000000000], [4920000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1,
      2)) (.next ([0, 0], [1080000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([0, -9000000000000], [5250000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([-720000000000], [6000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([-750000000000],
      [4200000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([-1305000000000], [5250000000000])
      (some (5, 1, 2)) (some (5, 1, 3)) (.next ([-1800000000000, -9000000000000], [6000000000000,
      0]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-1080000000000, -9000000000000],
      [2865000000000]) (some (5, 1, 3)) (some (5, 2, 3)) (.next ([-1080000000000, -9000000000000],
      [2160000000000, 18000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-6000000000000],
      [8145000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-4170000000000], [5250000000000])
      (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-4920000000000, 9000000000000], [5280000000000])
      (some (5, 2, 3)) (some (5, 2, 3)) (.terminal (some (5, 2, 3)) (some (0, 2, 3)) (some (5, 2,
      3))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded21_5 : ExcludedOn (model21.B 5 ++ [step21.q]) 9000000000000 (model21.caps 5)
    (model21.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_6 : ExcludedOn (model21.B 6 ++ [step21.q]) 9000000000000 (model21.caps 6)
    (model21.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_7 : ExcludedOn (model21.B 7 ++ [step21.q]) 9000000000000 (model21.caps 7)
    (model21.ord 7) 0 1 100 := by
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
    · exact excluded21_3
    · exact excluded21_4
    · exact excluded21_5
    · exact excluded21_6
    · exact excluded21_7
    · exact (hj rfl).elim
    · exact excluded21_9
theorem next21 : model21.insert step21 = model22 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded22_0 : ExcludedOn (model22.B 0 ++ [step22.q]) 9000000000000 (model22.caps 0)
    (model22.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_1 : ExcludedOn (model22.B 1 ++ [step22.q]) 9000000000000 (model22.caps 1)
    (model22.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_2 : ExcludedOn (model22.B 2 ++ [step22.q]) 9000000000000 (model22.caps 2)
    (model22.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_3 : ExcludedOn (model22.B 3 ++ [step22.q]) 9000000000000 (model22.caps 3)
    (model22.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4680000000000], [750000000000]) (some (2, 4, 2))
      (some (3, 4, 2)) (.next ([6705000000000], [1080000000000, 9000000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([2490000000000], [750000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([3600000000000, -9000000000000], [1830000000000, 9000000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([1410000000000, -9000000000000], [750000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([1440000000000], [3240000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([1275000000000], [4680000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [1080000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-750000000000],
      [5430000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1080000000000, -9000000000000],
      [7785000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-750000000000],
      [3240000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1830000000000, -9000000000000],
      [5430000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-750000000000], [2160000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3240000000000], [4680000000000])
      (some (0, 1, 2)) (some (4, 1, 2)) (.next ([-4680000000000], [5955000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.terminal (some (4, 1, 2)) (some (4, 2, 2)) (some (4, 2,
      2))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded22_5 : ExcludedOn (model22.B 5 ++ [step22.q]) 9000000000000 (model22.caps 5)
    (model22.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_6 : ExcludedOn (model22.B 6 ++ [step22.q]) 9000000000000 (model22.caps 6)
    (model22.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_7 : ExcludedOn (model22.B 7 ++ [step22.q]) 9000000000000 (model22.caps 7)
    (model22.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_8 : ExcludedOn (model22.B 8 ++ [step22.q]) 9000000000000 (model22.caps 8)
    (model22.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3615000000000], [2895000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([3240000000000], [6510000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([540000000000], [6135000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([165000000000], [3075000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [6135000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2895000000000], [6510000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6510000000000], [9750000000000]) (some (0, 1, 2))
      (some (0, 3, 2)) (.next ([-6135000000000], [6675000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-3075000000000], [3240000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_1 : ExcludedOn (model23.B 1 ++ [step23.q]) 9000000000000 (model23.caps 1)
    (model23.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_2 : ExcludedOn (model23.B 2 ++ [step23.q]) 9000000000000 (model23.caps 2)
    (model23.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_3 : ExcludedOn (model23.B 3 ++ [step23.q]) 9000000000000 (model23.caps 3)
    (model23.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_4 : ExcludedOn (model23.B 4 ++ [step23.q]) 9000000000000 (model23.caps 4)
    (model23.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6510000000000, 0], [330000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 5, 2)) (.next ([5280000000000], [720000000000])
      (some (3, 5, 2)) (some (3, 5, 2)) (.next ([6510000000000], [2790000000000]) (some (3, 5, 2))
      (some (3, 5, 2)) (.next ([4200000000000, -9000000000000], [1800000000000, 9000000000000])
      (some (3, 5, 2)) (some (3, 5, 2)) (.next ([1080000000000, 9000000000000], [1080000000000,
      9000000000000]) (some (3, 5, 2)) (some (3, 5, 2)) (.next ([1740000000000], [4260000000000])
      (some (3, 5, 2)) (some (3, 5, 2)) (.next ([1080000000000, 9000000000000], [3540000000000])
      (some (3, 5, 2)) (some (3, 5, 2)) (.next ([750000000000], [4680000000000, -9000000000000])
      (some (3, 5, 2)) (some (3, 5, 2)) (.next ([750000000000], [5760000000000]) (some (3, 5, 2))
      (some (4, 5, 2)) (.next ([510000000000], [4530000000000]) (some (4, 5, 2)) (some (4, 5, 2))
      (.next ([360000000000, 9000000000000], [4920000000000, -9000000000000]) (some (4, 5, 2)) (some
      (4, 5, 3)) (.next ([0, 0], [1080000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([-330000000000, -9000000000000], [6840000000000, 9000000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-720000000000], [6000000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-2790000000000], [9300000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-1800000000000, -9000000000000], [6000000000000, 0]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-1080000000000, -9000000000000], [2160000000000, 18000000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-4260000000000], [6000000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-3540000000000], [4620000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2, 3))
      (.next ([-4680000000000, 9000000000000], [5430000000000, -9000000000000]) (some (0, 2, 3))
      (some (0, 2, 3)) (.next ([-5760000000000], [6510000000000]) (some (0, 2, 3)) (some (0, 2, 3))
      (.next ([-4530000000000], [5040000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-4920000000000, 9000000000000], [5280000000000]) (some (0, 2, 3)) (some (0, 2, 3))
      (.terminal (some (0, 2, 3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded23_6 : ExcludedOn (model23.B 6 ++ [step23.q]) 9000000000000 (model23.caps 6)
    (model23.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_7 : ExcludedOn (model23.B 7 ++ [step23.q]) 9000000000000 (model23.caps 7)
    (model23.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_8 : ExcludedOn (model23.B 8 ++ [step23.q]) 9000000000000 (model23.caps 8)
    (model23.ord 8) 0 1 100 := by
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
    · exact (hj rfl).elim
    · exact excluded23_6
    · exact excluded23_7
    · exact excluded23_8
    · exact excluded23_9
theorem next23 : model23.insert step23 = model24 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Aown120000130000
end ConwaySoifer.Simplified.Certificates
