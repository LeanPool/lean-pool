/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown270000280000
import Mathlib.Tactic.FinCases

/-!
# Aown 270000 280000 1

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
namespace Aown270000280000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan9Owner0Part0 : FanWitness := (.next ([-601800000000, 2160000000000], [1393200000000,
    2160000000000]) (some (0, 6, 12)) (some (0, 6, 12)) (.next ([-1048200000000, -2160000000000],
    [2381400000000, 4320000000000]) (some (0, 6, 12)) (some (0, 6, 12)) (.next ([-210000000000],
    [465000000000]) (some (0, 6, 12)) (some (0, 6, 12)) (.next ([-4560000000000], [10005000000000])
    (some (0, 6, 12)) (some (1, 6, 12)) (.next ([-405000000000], [840000000000]) (some (1, 6, 12))
    (some (1, 6, 12)) (.next ([-4740000000000], [9810000000000]) (some (1, 6, 12)) (some (1, 6, 12))
    (.next ([-4138200000000, -2160000000000], [8416800000000, -2160000000000]) (some (1, 6, 12))
    (some (1, 6, 12)) (.next ([-4721400000000, -4320000000000], [9583200000000, 2160000000000])
    (some (1, 6, 12)) (some (1, 6, 12)) (.next ([-465000000000], [930000000000]) (some (1, 6, 12))
    (some (1, 12, 12)) (.next ([-195000000000], [375000000000]) (some (1, 12, 12)) (some (1, 12,
    12)) (.next ([-701400000000, -4320000000000], [1333200000000, 2160000000000]) (some (1, 12, 12))
    (some (1, 12, 12)) (.next ([-1333200000000, -2160000000000], [2381400000000, 4320000000000])
    (some (1, 12, 12)) (some (2, 12, 12)) (.next ([-631800000000, 2160000000000], [1048200000000,
    2160000000000]) (some (2, 12, 12)) (some (2, 12, 12)) (.next ([-750000000000], [1215000000000])
    (some (2, 12, 12)) (some (2, 12, 12)) (.next ([-1380000000000], [2190000000000]) (some (2, 12,
    12)) (some (2, 12, 12)) (.next ([-421800000000, 2160000000000], [583200000000, 2160000000000])
    (some (2, 12, 12)) (some (2, 12, 12)) (.next ([-1588200000000, -2160000000000], [2171400000000,
    4320000000000]) (some (2, 12, 12)) (some (2, 12, 12)) (.next ([-1166400000000, -4320000000000],
    [1588200000000, 2160000000000]) (some (2, 12, 12)) (some (2, 12, 12)) (.next ([-1590000000000],
    [1935000000000]) (some (2, 12, 12)) (some (2, 12, 12)) (.next ([-1215000000000],
    [1470000000000]) (some (2, 12, 12)) (some (2, 12, 12)) (.next ([-1768200000000, -2160000000000],
    [1976400000000, 4320000000000]) (some (2, 12, 12)) (some (2, 12, 12)) (.next ([-1631400000000,
    -4320000000000], [1798200000000, 2160000000000]) (some (2, 12, 12)) (some (2, 12, 12)) (.next
    ([-1798200000000, -2160000000000], [1916400000000, 4320000000000]) (some (2, 12, 12)) (some (2,
    12, 12)) (.next ([-1590000000000], [1650000000000]) (some (2, 12, 12)) (some (2, 12, 12))
    (.terminal (some (2, 12, 12)) (some (2, 12, 12)) (some (2, 12, 12)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan9Owner0Part1 : FanWitness := (.next ([345000000000], [1590000000000]) (some (11, 5, 12))
    (some (11, 5, 12)) (.next ([255000000000], [1215000000000]) (some (11, 5, 12)) (some (11, 5,
    12)) (.next ([208200000000, 2160000000000], [1768200000000, 2160000000000]) (some (11, 5, 12))
    (some (11, 5, 12)) (.next ([166800000000, -2160000000000], [1631400000000, 4320000000000]) (some
    (11, 5, 12)) (some (11, 5, 12)) (.next ([118200000000, 2160000000000], [1798200000000,
    2160000000000]) (some (11, 5, 12)) (some (11, 5, 12)) (.next ([60000000000], [1590000000000])
    (some (11, 5, 12)) (some (11, 5, 12)) (.next ([0], [285000000000]) (some (11, 5, 12)) (some (11,
    5, 12)) (.next ([-118200000000, -2160000000000], [1916400000000, 4320000000000]) (some (0, 6,
    12)) (some (0, 6, 12)) (.next ([-166800000000, 2160000000000], [1798200000000, 2160000000000])
    (some (0, 6, 12)) (some (0, 6, 12)) (.next ([-195000000000], [1380000000000]) (some (0, 6, 12))
    (some (0, 6, 12)) (.next ([-255000000000], [1470000000000]) (some (0, 6, 12)) (some (0, 6, 12))
    (.next ([-421800000000, 2160000000000], [1588200000000, 2160000000000]) (some (0, 6, 12)) (some
    (0, 6, 12)) (.next ([-583200000000, -2160000000000], [2171400000000, 4320000000000]) (some (0,
    6, 12)) (some (0, 6, 12)) (.next ([-210000000000], [750000000000]) (some (0, 6, 12)) (some (0,
    6, 12)) (.next ([-2550000000000], [9000000000000]) (some (0, 6, 12)) (some (0, 6, 12)) (.next
    ([-2805000000000], [9465000000000]) (some (0, 6, 12)) (some (0, 6, 12)) (.next ([-540000000000],
    [1755000000000]) (some (0, 6, 12)) (some (0, 6, 12)) (.next ([-3090000000000], [9750000000000])
    (some (0, 6, 12)) (some (0, 6, 12)) (.next ([-3555000000000], [10005000000000]) (some (0, 6,
    12)) (some (0, 6, 12)) (.next ([-405000000000], [1125000000000]) (some (0, 6, 12)) (some (0, 6,
    12)) (.next ([-2971800000000, 2160000000000], [7833600000000, -4320000000000]) (some (0, 6, 12))
    (some (0, 6, 12)) (.next ([-465000000000], [1215000000000]) (some (0, 6, 12)) (some (0, 6, 12))
    (.next ([-4020000000000], [10215000000000]) (some (0, 6, 12)) (some (0, 6, 12)) (.next
    ([-958200000000, -2160000000000], [2351400000000, 4320000000000]) (some (0, 6, 12)) (some (0, 6,
    12)) fan9Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan9Owner0Part2 : FanWitness := (.next ([6450000000000], [3555000000000]) (some (10, 3, 12))
    (some (10, 3, 12)) (.next ([720000000000], [405000000000]) (some (10, 3, 12)) (some (10, 3, 12))
    (.next ([4861800000000, -2160000000000], [2971800000000, -2160000000000]) (some (10, 3, 12))
    (some (10, 3, 12)) (.next ([750000000000], [465000000000]) (some (10, 3, 12)) (some (10, 3, 12))
    (.next ([6195000000000], [4020000000000]) (some (10, 3, 12)) (some (10, 3, 12)) (.next
    ([1393200000000, 2160000000000], [958200000000, 2160000000000]) (some (10, 3, 12)) (some (10, 3,
    12)) (.next ([791400000000, 4320000000000], [601800000000, -2160000000000]) (some (10, 3, 12))
    (some (10, 3, 12)) (.next ([1333200000000, 2160000000000], [1048200000000, 2160000000000]) (some
    (10, 3, 12)) (some (10, 3, 12)) (.next ([255000000000], [210000000000]) (some (10, 3, 12)) (some
    (10, 3, 12)) (.next ([5445000000000], [4560000000000]) (some (10, 3, 12)) (some (10, 4, 12))
    (.next ([435000000000], [405000000000]) (some (10, 4, 12)) (some (10, 4, 12)) (.next
    ([5070000000000], [4740000000000]) (some (10, 4, 12)) (some (10, 4, 12)) (.next ([4278600000000,
    -4320000000000], [4138200000000, 2160000000000]) (some (10, 4, 12)) (some (10, 4, 12)) (.next
    ([4861800000000, -2160000000000], [4721400000000, 4320000000000]) (some (10, 4, 12)) (some (10,
    4, 12)) (.next ([465000000000], [465000000000]) (some (10, 4, 12)) (some (10, 4, 12)) (.next
    ([180000000000], [195000000000]) (some (10, 4, 12)) (some (10, 4, 12)) (.next ([631800000000,
    -2160000000000], [701400000000, 4320000000000]) (some (10, 4, 12)) (some (10, 5, 12)) (.next
    ([1048200000000, 2160000000000], [1333200000000, 2160000000000]) (some (10, 5, 12)) (some (11,
    5, 12)) (.next ([416400000000, 4320000000000], [631800000000, -2160000000000]) (some (11, 5,
    12)) (some (11, 5, 12)) (.next ([465000000000], [750000000000]) (some (11, 5, 12)) (some (11, 5,
    12)) (.next ([810000000000], [1380000000000]) (some (11, 5, 12)) (some (11, 5, 12)) (.next
    ([161400000000, 4320000000000], [421800000000, -2160000000000]) (some (11, 5, 12)) (some (11, 5,
    12)) (.next ([583200000000, 2160000000000], [1588200000000, 2160000000000]) (some (11, 5, 12))
    (some (11, 5, 12)) (.next ([421800000000, -2160000000000], [1166400000000, 4320000000000]) (some
    (11, 5, 12)) (some (11, 5, 12)) fan9Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan10Owner0Part0 : FanWitness := (.next ([-3435000000000], [9135000000000]) (some (0, 6, 12))
    (some (0, 6, 12)) (.next ([-465000000000], [1215000000000]) (some (0, 6, 12)) (some (0, 6, 12))
    (.next ([-3416400000000, -4320000000000], [8908200000000, 2160000000000]) (some (0, 6, 12))
    (some (0, 6, 12)) (.next ([-958200000000, -2160000000000], [2351400000000, 4320000000000]) (some
    (0, 6, 12)) (some (0, 12, 12)) (.next ([-601800000000, 2160000000000], [1393200000000,
    2160000000000]) (some (0, 12, 12)) (some (0, 12, 12)) (.next ([-1048200000000, -2160000000000],
    [2381400000000, 4320000000000]) (some (0, 12, 12)) (some (0, 12, 12)) (.next ([-210000000000],
    [465000000000]) (some (0, 12, 12)) (some (0, 12, 12)) (.next ([-405000000000], [840000000000])
    (some (0, 12, 12)) (some (1, 12, 12)) (.next ([-465000000000], [930000000000]) (some (1, 12,
    12)) (some (1, 12, 12)) (.next ([-195000000000], [375000000000]) (some (1, 12, 12)) (some (1,
    12, 12)) (.next ([-701400000000, -4320000000000], [1333200000000, 2160000000000]) (some (1, 12,
    12)) (some (1, 12, 12)) (.next ([-1333200000000, -2160000000000], [2381400000000,
    4320000000000]) (some (1, 12, 12)) (some (2, 12, 12)) (.next ([-631800000000, 2160000000000],
    [1048200000000, 2160000000000]) (some (2, 12, 12)) (some (2, 12, 12)) (.next ([-750000000000],
    [1215000000000]) (some (2, 12, 12)) (some (2, 12, 12)) (.next ([-1380000000000],
    [2190000000000]) (some (2, 12, 12)) (some (2, 12, 12)) (.next ([-421800000000, 2160000000000],
    [583200000000, 2160000000000]) (some (2, 12, 12)) (some (2, 12, 12)) (.next ([-1588200000000,
    -2160000000000], [2171400000000, 4320000000000]) (some (2, 12, 12)) (some (2, 12, 12)) (.next
    ([-1166400000000, -4320000000000], [1588200000000, 2160000000000]) (some (2, 12, 12)) (some (2,
    12, 12)) (.next ([-1590000000000], [1935000000000]) (some (2, 12, 12)) (some (2, 12, 12)) (.next
    ([-1215000000000], [1470000000000]) (some (2, 12, 12)) (some (2, 12, 12)) (.next
    ([-1768200000000, -2160000000000], [1976400000000, 4320000000000]) (some (2, 12, 12)) (some (2,
    12, 12)) (.next ([-1631400000000, -4320000000000], [1798200000000, 2160000000000]) (some (2, 12,
    12)) (some (2, 12, 12)) (.next ([-1798200000000, -2160000000000], [1916400000000,
    4320000000000]) (some (2, 12, 12)) (some (2, 12, 12)) (.next ([-1590000000000], [1650000000000])
    (some (2, 12, 12)) (some (2, 12, 12)) (.terminal (some (2, 12, 12)) (some (2, 12, 12)) (some (2,
    12, 12)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan10Owner0Part1 : FanWitness := (.next ([208200000000, 2160000000000], [1768200000000,
    2160000000000]) (some (11, 5, 12)) (some (11, 5, 12)) (.next ([166800000000, -2160000000000],
    [1631400000000, 4320000000000]) (some (11, 5, 12)) (some (11, 5, 12)) (.next ([118200000000,
    2160000000000], [1798200000000, 2160000000000]) (some (11, 5, 12)) (some (11, 5, 12)) (.next
    ([60000000000], [1590000000000]) (some (11, 5, 12)) (some (11, 5, 12)) (.next ([0],
    [285000000000]) (some (11, 5, 12)) (some (11, 5, 12)) (.next ([-118200000000, -2160000000000],
    [1916400000000, 4320000000000]) (some (0, 6, 12)) (some (0, 6, 12)) (.next ([-166800000000,
    2160000000000], [1798200000000, 2160000000000]) (some (0, 6, 12)) (some (0, 6, 12)) (.next
    ([-1083600000000, 4320000000000], [7741800000000, -2160000000000]) (some (0, 6, 12)) (some (0,
    6, 12)) (.next ([-195000000000], [1380000000000]) (some (0, 6, 12)) (some (0, 6, 12)) (.next
    ([-1245000000000], [8325000000000]) (some (0, 6, 12)) (some (0, 6, 12)) (.next
    ([-1500000000000], [8790000000000]) (some (0, 6, 12)) (some (0, 6, 12)) (.next ([-255000000000],
    [1470000000000]) (some (0, 6, 12)) (some (0, 6, 12)) (.next ([-1785000000000], [9075000000000])
    (some (0, 6, 12)) (some (0, 6, 12)) (.next ([-1666800000000, 2160000000000], [7158600000000,
    -4320000000000]) (some (0, 6, 12)) (some (0, 6, 12)) (.next ([-2250000000000], [9330000000000])
    (some (0, 6, 12)) (some (0, 6, 12)) (.next ([-421800000000, 2160000000000], [1588200000000,
    2160000000000]) (some (0, 6, 12)) (some (0, 6, 12)) (.next ([-583200000000, -2160000000000],
    [2171400000000, 4320000000000]) (some (0, 6, 12)) (some (0, 6, 12)) (.next ([-210000000000],
    [750000000000]) (some (0, 6, 12)) (some (0, 6, 12)) (.next ([-2715000000000], [9540000000000])
    (some (0, 6, 12)) (some (0, 6, 12)) (.next ([-540000000000], [1755000000000]) (some (0, 6, 12))
    (some (0, 6, 12)) (.next ([-3000000000000], [9540000000000]) (some (0, 6, 12)) (some (0, 6, 12))
    (.next ([-3255000000000], [9330000000000]) (some (0, 6, 12)) (some (0, 6, 12)) (.next
    ([-405000000000], [1125000000000]) (some (0, 6, 12)) (some (0, 6, 12)) (.next ([-2833200000000,
    -2160000000000], [7741800000000, -2160000000000]) (some (0, 6, 12)) (some (0, 6, 12))
    fan10Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan10Owner0Part2 : FanWitness := (.next ([6540000000000], [3000000000000]) (some (9, 3, 12))
    (some (10, 3, 12)) (.next ([6075000000000], [3255000000000]) (some (10, 3, 12)) (some (10, 3,
    12)) (.next ([720000000000], [405000000000]) (some (10, 3, 12)) (some (10, 3, 12)) (.next
    ([4908600000000, -4320000000000], [2833200000000, 2160000000000]) (some (10, 3, 12)) (some (10,
    3, 12)) (.next ([5700000000000], [3435000000000]) (some (10, 3, 12)) (some (10, 3, 12)) (.next
    ([750000000000], [465000000000]) (some (10, 3, 12)) (some (10, 3, 12)) (.next ([5491800000000,
    -2160000000000], [3416400000000, 4320000000000]) (some (10, 3, 12)) (some (10, 3, 12)) (.next
    ([1393200000000, 2160000000000], [958200000000, 2160000000000]) (some (10, 3, 12)) (some (10, 3,
    12)) (.next ([791400000000, 4320000000000], [601800000000, -2160000000000]) (some (10, 3, 12))
    (some (10, 3, 12)) (.next ([1333200000000, 2160000000000], [1048200000000, 2160000000000]) (some
    (10, 3, 12)) (some (10, 3, 12)) (.next ([255000000000], [210000000000]) (some (10, 3, 12)) (some
    (10, 3, 12)) (.next ([435000000000], [405000000000]) (some (10, 3, 12)) (some (10, 4, 12))
    (.next ([465000000000], [465000000000]) (some (10, 4, 12)) (some (10, 4, 12)) (.next
    ([180000000000], [195000000000]) (some (10, 4, 12)) (some (10, 4, 12)) (.next ([631800000000,
    -2160000000000], [701400000000, 4320000000000]) (some (10, 4, 12)) (some (10, 5, 12)) (.next
    ([1048200000000, 2160000000000], [1333200000000, 2160000000000]) (some (10, 5, 12)) (some (11,
    5, 12)) (.next ([416400000000, 4320000000000], [631800000000, -2160000000000]) (some (11, 5,
    12)) (some (11, 5, 12)) (.next ([465000000000], [750000000000]) (some (11, 5, 12)) (some (11, 5,
    12)) (.next ([810000000000], [1380000000000]) (some (11, 5, 12)) (some (11, 5, 12)) (.next
    ([161400000000, 4320000000000], [421800000000, -2160000000000]) (some (11, 5, 12)) (some (11, 5,
    12)) (.next ([583200000000, 2160000000000], [1588200000000, 2160000000000]) (some (11, 5, 12))
    (some (11, 5, 12)) (.next ([421800000000, -2160000000000], [1166400000000, 4320000000000]) (some
    (11, 5, 12)) (some (11, 5, 12)) (.next ([345000000000], [1590000000000]) (some (11, 5, 12))
    (some (11, 5, 12)) (.next ([255000000000], [1215000000000]) (some (11, 5, 12)) (some (11, 5,
    12)) fan10Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan13Owner2Part0 : FanWitness := (.next ([6570000000000, -9000000000000], [2430000000000,
    9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([5445000000000, 0], [2430000000000,
    9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([675000000000], [630000000000]) (some
    (0, 4, 1)) (some (0, 4, 1)) (.next ([2376000000000], [3450000000000]) (some (0, 4, 1)) (some (0,
    4, 2)) (.next ([1695000000000, -9000000000000], [2679000000000, 9000000000000]) (some (0, 1, 2))
    (some (0, 1, 2)) (.next ([2196000000000, -9000000000000], [4125000000000, 0]) (some (0, 1, 2))
    (some (0, 1, 2)) (.next ([1071000000000], [4125000000000]) (some (0, 1, 2)) (some (0, 1, 2))
    (.next ([1320000000000], [5430000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
    ([645000000000], [4800000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([645000000000, 0],
    [5925000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([396000000000],
    [4374000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0], [3075000000000,
    9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1755000000000, -9000000000000],
    [8505000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2430000000000,
    -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2430000000000,
    -9000000000000], [7875000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-630000000000], [1305000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3450000000000],
    [5826000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2679000000000, -9000000000000],
    [4374000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-4125000000000, 0], [6321000000000,
    -9000000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.next ([-4125000000000], [5196000000000])
    (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-5430000000000], [6750000000000]) (some (4, 1, 3))
    (some (4, 1, 3)) (.next ([-4800000000000], [5445000000000]) (some (4, 1, 3)) (some (4, 1, 3))
    (.next ([-5925000000000, 9000000000000], [6570000000000, -9000000000000]) (some (4, 1, 3)) (some
    (4, 1, 3)) (.next ([-4374000000000], [4770000000000]) (some (4, 1, 3)) (some (4, 1, 3))
    (.terminal (some (4, 1, 3)) (some (4, 1, 0)) (some (4, 1, 3)))))))))))))))))))))))))))

theorem excluded8_0 : ExcludedOn (model8.B 0 ++ [step8.q]) 9000000000000 (model8.caps 0) (model8.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_1 : ExcludedOn (model8.B 1 ++ [step8.q]) 9000000000000 (model8.caps 1) (model8.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_6 : ExcludedOn (model8.B 6 ++ [step8.q]) 9000000000000 (model8.caps 6) (model8.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_7 : ExcludedOn (model8.B 7 ++ [step8.q]) 9000000000000 (model8.caps 7) (model8.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2430000000000, 9000000000000], [4140000000000,
      -18000000000000]) (some (2, 0, 1)) (some (4, 0, 2)) (.next ([2430000000000, 9000000000000],
      [5925000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([2430000000000,
      9000000000000], [6570000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([645000000000, 0], [5925000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([0, 0], [6570000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([-4140000000000, 18000000000000], [6570000000000, -9000000000000]) (some (4, 0, 2)) (some (4,
      0, 2)) (.next ([-5925000000000, 9000000000000], [8355000000000]) (some (4, 0, 2)) (some (4, 1,
      2)) (.next ([-6570000000000, 9000000000000], [9000000000000, 0]) (some (4, 1, 2)) (some (4, 1,
      2)) (.next ([-5925000000000, 9000000000000], [6570000000000, -9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
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

theorem excluded9_0 : ExcludedOn (model9.B 0 ++ [step9.q]) 9000000000000 (model9.caps 0) (model9.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1798200000000, 2160000000000], [118200000000,
      2160000000000]) (some (12, 2, 12)) (some (12, 3, 12)) (.next ([1631400000000, 4320000000000],
      [166800000000, -2160000000000]) (some (12, 3, 12)) (some (12, 3, 12)) (.next ([1185000000000],
      [195000000000]) (some (12, 3, 12)) (some (12, 3, 12)) (.next ([1215000000000], [255000000000])
      (some (12, 3, 12)) (some (12, 3, 12)) (.next ([1166400000000, 4320000000000], [421800000000,
      -2160000000000]) (some (12, 3, 12)) (some (12, 3, 12)) (.next ([1588200000000, 2160000000000],
      [583200000000, 2160000000000]) (some (12, 3, 12)) (some (12, 3, 12)) (.next ([540000000000],
      [210000000000]) (some (12, 3, 12)) (some (12, 3, 12)) (.next ([6450000000000],
      [2550000000000]) (some (12, 3, 12)) (some (9, 3, 12)) (.next ([6660000000000],
      [2805000000000]) (some (9, 3, 12)) (some (9, 3, 12)) (.next ([1215000000000], [540000000000])
      (some (9, 3, 12)) (some (9, 3, 12)) (.next ([6660000000000], [3090000000000]) (some (9, 3,
      12)) (some (10, 3, 12)) fan9Owner0Part2)))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_1 : ExcludedOn (model9.B 1 ++ [step9.q]) 9000000000000 (model9.caps 1) (model9.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3555000000000], [945000000000]) none none (.next
      ([2430000000000, 9000000000000], [2070000000000, -9000000000000]) none none (.next
      ([2430000000000, 9000000000000], [2430000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([2430000000000, 9000000000000], [3555000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([0, 0], [1125000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-945000000000], [4500000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2070000000000,
      9000000000000], [4500000000000, 0]) (some (3, 1, 2)) none (.next ([-2430000000000,
      -9000000000000], [4860000000000, 18000000000000]) none none (.next ([-3555000000000],
      [5985000000000, 9000000000000]) none none (.terminal none none none))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([3555000000000], [3015000000000, -9000000000000])
      (some (2, 0, 1)) (some (3, 0, 2)) (.next ([3555000000000], [5445000000000]) (some (3, 0, 2))
      (some (3, 0, 2)) (.next ([2430000000000, 9000000000000], [4140000000000, -18000000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2430000000000, 9000000000000], [6570000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1125000000000, -9000000000000],
      [5445000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [6570000000000,
      -9000000000000]) (some (3, 0, 2)) (some (4, 0, 2)) (.next ([-3015000000000, 9000000000000],
      [6570000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-5445000000000],
      [9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-4140000000000, 18000000000000],
      [6570000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-6570000000000,
      9000000000000], [9000000000000, 0]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([-5445000000000,
      0], [6570000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.terminal (some (4, 1,
      2)) (some (0, 1, 2)) (some (4, 1, 2))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded9_0
    · exact excluded9_1
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.witnessedFan (.next ([1798200000000, 2160000000000], [118200000000,
      2160000000000]) (some (12, 2, 12)) (some (12, 3, 12)) (.next ([1631400000000, 4320000000000],
      [166800000000, -2160000000000]) (some (12, 3, 12)) (some (12, 3, 12)) (.next ([6658200000000,
      2160000000000], [1083600000000, -4320000000000]) (some (12, 3, 12)) (some (12, 3, 12)) (.next
      ([1185000000000], [195000000000]) (some (9, 3, 12)) (some (9, 3, 12)) (.next ([7080000000000],
      [1245000000000]) (some (9, 3, 12)) (some (9, 3, 12)) (.next ([7290000000000], [1500000000000])
      (some (9, 3, 12)) (some (9, 3, 12)) (.next ([1215000000000], [255000000000]) (some (9, 3, 12))
      (some (9, 3, 12)) (.next ([7290000000000], [1785000000000]) (some (9, 3, 12)) (some (9, 3,
      12)) (.next ([5491800000000, -2160000000000], [1666800000000, -2160000000000]) (some (9, 3,
      12)) (some (9, 3, 12)) (.next ([7080000000000], [2250000000000]) (some (9, 3, 12)) (some (9,
      3, 12)) (.next ([1166400000000, 4320000000000], [421800000000, -2160000000000]) (some (9, 3,
      12)) (some (9, 3, 12)) (.next ([1588200000000, 2160000000000], [583200000000, 2160000000000])
      (some (9, 3, 12)) (some (9, 3, 12)) (.next ([540000000000], [210000000000]) (some (9, 3, 12))
      (some (9, 3, 12)) (.next ([6825000000000], [2715000000000]) (some (9, 3, 12)) (some (9, 3,
      12)) (.next ([1215000000000], [540000000000]) (some (9, 3, 12)) (some (9, 3, 12))
      fan10Owner0Part2))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded10_1 : ExcludedOn (model10.B 1 ++ [step10.q]) 9000000000000 (model10.caps 1)
    (model10.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([495000000000, -9000000000000], [180000000000,
      9000000000000]) none none (.next ([2925000000000], [2250000000000]) none none (.next
      ([2430000000000, 9000000000000], [2070000000000, -9000000000000]) none none (.next
      ([2430000000000, 9000000000000], [2430000000000, 9000000000000]) none none (.next
      ([1755000000000, 9000000000000], [2925000000000]) none none (.next ([0], [6930000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-180000000000, -9000000000000],
      [675000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2250000000000],
      [5175000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2070000000000, 9000000000000],
      [4500000000000, 0]) (some (3, 1, 2)) none (.next ([-2430000000000, -9000000000000],
      [4860000000000, 18000000000000]) none none (.next ([-2925000000000], [4680000000000,
      9000000000000]) none none (.terminal none none none))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_7 : ExcludedOn (model10.B 7 ++ [step10.q]) 9000000000000 (model10.caps 7)
    (model10.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([495000000000, -9000000000000], [180000000000,
      9000000000000]) (some (2, 4, 1)) (some (3, 4, 2)) (.next ([2925000000000], [4320000000000,
      -9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([2430000000000, 9000000000000],
      [4140000000000, -18000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([2925000000000],
      [6750000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([2430000000000, 9000000000000],
      [6570000000000, -9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([495000000000,
      -9000000000000], [6750000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0, 0],
      [6570000000000, -9000000000000]) (some (3, 4, 2)) (some (4, 4, 2)) (.next ([-180000000000,
      -9000000000000], [675000000000, 0]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([-4320000000000,
      9000000000000], [7245000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([-4140000000000, 18000000000000], [6570000000000, -9000000000000]) (some (4, 0, 2)) (some (4,
      0, 2)) (.next ([-6750000000000], [9675000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next
      ([-6570000000000, 9000000000000], [9000000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-6750000000000, 0], [7245000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.terminal (some (4, 1, 2)) (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded10_0
    · exact excluded10_1
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 0 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_2 : ExcludedOn (model11.B 2 ++ [step11.q]) 9000000000000 (model11.caps 2)
    (model11.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_7 : ExcludedOn (model11.B 7 ++ [step11.q]) 9000000000000 (model11.caps 7)
    (model11.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2430000000000, 9000000000000], [2235000000000,
      -9000000000000]) (some (2, 0, 1)) (some (3, 0, 2)) (.next ([1905000000000, -9000000000000],
      [2430000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2430000000000,
      9000000000000], [4140000000000, -18000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([2430000000000, 9000000000000], [6570000000000, -9000000000000]) (some (3, 0, 2)) (some (3,
      0, 2)) (.next ([0, 0], [6570000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2))
      (.next ([-2235000000000, 9000000000000], [4665000000000, 0]) (some (0, 0, 2)) (some (0, 0, 2))
      (.next ([-2430000000000, -9000000000000], [4335000000000]) (some (0, 0, 2)) (some (0, 4, 2))
      (.next ([-4140000000000, 18000000000000], [6570000000000, -9000000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-6570000000000, 9000000000000], [9000000000000, 0]) (some (0, 4, 2))
      (some (0, 4, 2)) (.terminal (some (0, 4, 2)) (some (0, 1, 2)) (some (0, 4, 2))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded11_2
    · exact excluded11_3
    · exact excluded11_4
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
  apply ExclusionHint.sound (.pair 0 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_1 : ExcludedOn (model12.B 1 ++ [step12.q]) 9000000000000 (model12.caps 1)
    (model12.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2430000000000, 9000000000000], [2235000000000,
      -9000000000000]) none none (.next ([2430000000000, 9000000000000], [2430000000000,
      9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([2430000000000, 9000000000000],
      [2985000000000, -9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([0],
      [7095000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2235000000000,
      9000000000000], [4665000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2430000000000,
      -9000000000000], [4860000000000, 18000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-2985000000000, 9000000000000], [5415000000000, 0]) (some (0, 1, 3)) (some (1, 1, 3))
      (.terminal (some (1, 1, 3)) none none))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded12_2 : ExcludedOn (model12.B 2 ++ [step12.q]) 9000000000000 (model12.caps 2)
    (model12.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded12_5
    · exact excluded12_6
    · exact (hj rfl).elim
    · exact excluded12_8
    · exact excluded12_9
theorem next12 : model12.insert step12 = model13 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded13_1 : ExcludedOn (model13.B 1 ++ [step13.q]) 9000000000000 (model13.caps 1)
    (model13.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8751000000000], [39000000000]) none none (.next
      ([7056000000000, 9000000000000], [1695000000000, -9000000000000]) none none (.next
      ([2430000000000, 9000000000000], [2235000000000, -9000000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([2430000000000, 9000000000000], [2430000000000, 9000000000000]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([2196000000000, -9000000000000], [4125000000000, 0]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([0], [7095000000000, 9000000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([-39000000000], [8790000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-1695000000000, 9000000000000], [8751000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-2235000000000, 9000000000000], [4665000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-2430000000000, -9000000000000], [4860000000000, 18000000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([-4125000000000, 0], [6321000000000, -9000000000000]) (some (3, 1, 2)) (some
      (3, 1, 2)) (.terminal (some (3, 1, 2)) none none))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_2 : ExcludedOn (model13.B 2 ++ [step13.q]) 9000000000000 (model13.caps 2)
    (model13.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6750000000000, 0], [1755000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) fan13Owner2Part0)) (den := 9000000000000)
      (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_3 : ExcludedOn (model13.B 3 ++ [step13.q]) 9000000000000 (model13.caps 3)
    (model13.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4374000000000, 0], [2445000000000,
      -9000000000000]) (some (1, 0, 3)) (some (2, 0, 3)) (.next ([2430000000000, 9000000000000],
      [2430000000000, 9000000000000]) (some (2, 0, 3)) (some (2, 0, 3)) (.next ([4374000000000],
      [4875000000000]) (some (2, 0, 3)) (some (2, 0, 3)) (.next ([1944000000000, -9000000000000],
      [7305000000000, 9000000000000]) (some (2, 0, 3)) (some (2, 0, 3)) (.next ([0], [2430000000000,
      9000000000000]) (some (2, 0, 3)) (some (2, 3, 3)) (.next ([-2445000000000, 9000000000000],
      [6819000000000, -9000000000000]) (some (0, 3, 3)) (some (0, 3, 3)) (.next ([-2430000000000,
      -9000000000000], [4860000000000, 18000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([-4875000000000], [9249000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-7305000000000,
      -9000000000000], [9249000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.terminal (some (0, 3,
      1)) (some (0, 3, 1)) (some (0, 3, 1))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_4 : ExcludedOn (model13.B 4 ++ [step13.q]) 9000000000000 (model13.caps 4)
    (model13.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded13_1
    · exact excluded13_2
    · exact excluded13_3
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
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_1 : ExcludedOn (model14.B 1 ++ [step14.q]) 9000000000000 (model14.caps 1)
    (model14.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_3 : ExcludedOn (model14.B 3 ++ [step14.q]) 9000000000000 (model14.caps 3)
    (model14.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_4 : ExcludedOn (model14.B 4 ++ [step14.q]) 9000000000000 (model14.caps 4)
    (model14.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([3585000000000], [2985000000000]) (some (2, 0,
      1)) (some (4, 0, 2)) (.next ([2430000000000, 9000000000000], [2985000000000, -9000000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([2430000000000, 0], [4140000000000, -9000000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([1155000000000, -9000000000000], [2430000000000,
      9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([2430000000000, 9000000000000],
      [6570000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([0, 0],
      [6570000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-2985000000000],
      [6570000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-2985000000000, 9000000000000],
      [5415000000000, 0]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-4140000000000, 9000000000000],
      [6570000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([-2430000000000,
      -9000000000000], [3585000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6570000000000,
      9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded14_3
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
  apply ExclusionHint.sound (.pair 2 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_1 : ExcludedOn (model15.B 1 ++ [step15.q]) 9000000000000 (model15.caps 1)
    (model15.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2925000000000], [1665000000000]) none none
      (.next ([2430000000000, 9000000000000], [2235000000000, -9000000000000]) none none (.next
      ([2430000000000, 9000000000000], [2430000000000, 9000000000000]) none none (.next
      ([2505000000000, 9000000000000], [2925000000000]) none none (.next ([75000000000, 0],
      [495000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0], [7095000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1665000000000], [4590000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2235000000000, 9000000000000], [4665000000000, 0])
      (some (3, 1, 2)) none (.next ([-2430000000000, -9000000000000], [4860000000000,
      18000000000000]) none none (.next ([-2925000000000], [5430000000000, 9000000000000]) none none
      (.next ([-495000000000, 9000000000000], [570000000000, -9000000000000]) none none (.terminal
      none none none))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded15_3 : ExcludedOn (model15.B 3 ++ [step15.q]) 9000000000000 (model15.caps 3)
    (model15.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_4 : ExcludedOn (model15.B 4 ++ [step15.q]) 9000000000000 (model15.caps 4)
    (model15.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_5 : ExcludedOn (model15.B 5 ++ [step15.q]) 9000000000000 (model15.caps 5)
    (model15.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_6 : ExcludedOn (model15.B 6 ++ [step15.q]) 9000000000000 (model15.caps 6)
    (model15.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_7 : ExcludedOn (model15.B 7 ++ [step15.q]) 9000000000000 (model15.caps 7)
    (model15.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2925000000000], [2415000000000]) (some (2, 0,
      1)) (some (3, 0, 2)) (.next ([2430000000000, 9000000000000], [2985000000000, -9000000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2925000000000], [6000000000000]) (some (3, 0, 2))
      (some (3, 0, 2)) (.next ([1155000000000, -9000000000000], [2430000000000, 9000000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2430000000000, 9000000000000], [6570000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([75000000000, 0], [495000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([495000000000, -9000000000000],
      [6000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [6570000000000,
      -9000000000000]) (some (3, 0, 2)) (some (4, 0, 2)) (.next ([-2415000000000], [5340000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-2985000000000, 9000000000000], [5415000000000, 0])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-6000000000000], [8925000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([-2430000000000, -9000000000000], [3585000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([-6570000000000, 9000000000000], [9000000000000, 0]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([-495000000000, 9000000000000], [570000000000, -9000000000000]) (some
      (4, 1, 2)) (some (4, 1, 2)) (.next ([-6000000000000, 0], [6495000000000, -9000000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1, 2)) (some (0, 1,
      2))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded15_3
    · exact excluded15_4
    · exact excluded15_5
    · exact excluded15_6
    · exact excluded15_7
    · exact excluded15_8
    · exact excluded15_9
theorem next15 : model15.insert step15 = model16 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Aown270000280000
end ConwaySoifer.Simplified.Certificates
