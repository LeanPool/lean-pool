/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown210000220000
import Mathlib.Tactic.FinCases

/-!
# Aown 210000 220000 1

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
namespace Aown210000220000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan8Owner0Part0 : FanWitness := (.next ([-375000000000], [2895000000000]) (some (0, 4, 9)) (some
    (0, 4, 9)) (.next ([-255000000000], [1635000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next
    ([-1455000000000], [8250000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-1477200000000,
    4680000000000], [8133600000000, -2340000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next
    ([-1830000000000], [9000000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-630000000000],
    [2895000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-2085000000000], [9255000000000])
    (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-2835000000000], [9630000000000]) (some (0, 4, 9))
    (some (0, 4, 9)) (.next ([-3090000000000], [9630000000000]) (some (0, 4, 9)) (some (0, 4, 9))
    (.next ([-2460000000000], [6735000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next
    ([-375000000000], [1005000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-3465000000000],
    [9255000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-3465000000000], [9000000000000])
    (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-1005000000000], [2520000000000]) (some (0, 4, 9))
    (some (0, 9, 9)) (.next ([-352800000000, -4680000000000], [866400000000, 2340000000000]) (some
    (0, 9, 9)) (some (0, 9, 9)) (.next ([-375000000000], [750000000000]) (some (0, 9, 9)) (some (0,
    9, 9)) (.next ([-607800000000, -4680000000000], [1121400000000, 2340000000000]) (some (0, 9, 9))
    (some (1, 9, 9)) (.next ([-1398600000000, 2340000000000], [2381400000000, 2340000000000]) (some
    (1, 9, 9)) (some (1, 9, 9)) (.next ([-1515000000000], [2520000000000]) (some (1, 9, 9)) (some
    (1, 9, 9)) (.next ([-630000000000], [1005000000000]) (some (1, 9, 9)) (some (1, 9, 9)) (.next
    ([-2265000000000], [2895000000000]) (some (1, 9, 9)) (some (1, 9, 9)) (.next ([-1380000000000],
    [1635000000000]) (some (1, 9, 9)) (some (1, 9, 9)) (.next ([-2520000000000], [2895000000000])
    (some (1, 9, 9)) (some (1, 9, 9)) (.next ([-1357800000000, -4680000000000], [1496400000000,
    2340000000000]) (some (1, 9, 9)) (some (1, 9, 9)) (.terminal (some (1, 9, 9)) (some (1, 9, 9))
    (some (1, 9, 9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan8Owner0Part1 : FanWitness := (.next ([6795000000000], [1455000000000]) (some (9, 2, 9)) (some
    (9, 2, 9)) (.next ([6656400000000, 2340000000000], [1477200000000, -4680000000000]) (some (7, 2,
    9)) (some (7, 2, 9)) (.next ([7170000000000], [1830000000000]) (some (7, 2, 9)) (some (7, 2, 9))
    (.next ([2265000000000], [630000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next
    ([7170000000000], [2085000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next ([6795000000000],
    [2835000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next ([6540000000000], [3090000000000])
    (some (7, 2, 9)) (some (7, 2, 9)) (.next ([4275000000000], [2460000000000]) (some (7, 2, 9))
    (some (7, 2, 9)) (.next ([630000000000], [375000000000]) (some (7, 2, 9)) (some (7, 2, 9))
    (.next ([5790000000000], [3465000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next
    ([5535000000000], [3465000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next ([1515000000000],
    [1005000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next ([513600000000, -2340000000000],
    [352800000000, 4680000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next ([375000000000],
    [375000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next ([513600000000, -2340000000000],
    [607800000000, 4680000000000]) (some (7, 2, 9)) (some (8, 3, 9)) (.next ([982800000000,
    4680000000000], [1398600000000, -2340000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next
    ([1005000000000], [1515000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([375000000000],
    [630000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([630000000000], [2265000000000]) (some
    (8, 3, 9)) (some (8, 3, 9)) (.next ([255000000000], [1380000000000]) (some (8, 3, 9)) (some (8,
    3, 9)) (.next ([375000000000], [2520000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next
    ([138600000000, -2340000000000], [1357800000000, 4680000000000]) (some (8, 3, 9)) (some (8, 3,
    9)) (.next ([0], [1380000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([-116400000000,
    -2340000000000], [1612800000000, 4680000000000]) (some (0, 3, 9)) (some (0, 4, 9))
    fan8Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan9Owner0Part0 : FanWitness := (.next ([-375000000000], [2895000000000]) (some (0, 9, 9)) (some
    (0, 9, 9)) (.next ([-255000000000], [1635000000000]) (some (0, 9, 9)) (some (0, 9, 9)) (.next
    ([-630000000000], [2895000000000]) (some (0, 9, 9)) (some (0, 9, 9)) (.next ([-375000000000],
    [1005000000000]) (some (0, 9, 9)) (some (0, 9, 9)) (.next ([-1005000000000], [2520000000000])
    (some (0, 9, 9)) (some (0, 9, 9)) (.next ([-352800000000, -4680000000000], [866400000000,
    2340000000000]) (some (0, 9, 9)) (some (0, 9, 9)) (.next ([-375000000000], [750000000000]) (some
    (0, 9, 9)) (some (0, 9, 9)) (.next ([-3708000000000], [7110000000000]) (some (0, 9, 9)) (some
    (1, 9, 9)) (.next ([-5106600000000, 2340000000000], [9491400000000, 2340000000000]) (some (1, 9,
    5)) (some (1, 9, 5)) (.next ([-5223000000000], [9630000000000]) (some (1, 9, 5)) (some (1, 9,
    5)) (.next ([-1121400000000, -2340000000000], [1987800000000, 4680000000000]) (some (1, 9, 5))
    (some (1, 9, 5)) (.next ([-1398600000000, 2340000000000], [2381400000000, 2340000000000]) (some
    (1, 9, 5)) (some (1, 9, 5)) (.next ([-5973000000000], [10005000000000]) (some (1, 9, 5)) (some
    (1, 9, 6)) (.next ([-1515000000000], [2520000000000]) (some (1, 9, 6)) (some (1, 9, 6)) (.next
    ([-6228000000000], [10005000000000]) (some (1, 9, 6)) (some (1, 9, 6)) (.next ([-630000000000],
    [1005000000000]) (some (1, 9, 6)) (some (1, 9, 6)) (.next ([-6603000000000], [9630000000000])
    (some (1, 9, 6)) (some (1, 9, 6)) (.next ([-6603000000000], [9375000000000]) (some (1, 9, 6))
    (some (1, 9, 6)) (.next ([-5973000000000], [8370000000000]) (some (1, 9, 6)) (some (1, 9, 6))
    (.next ([-6228000000000], [8625000000000]) (some (1, 9, 6)) (some (1, 9, 6)) (.next
    ([-2265000000000], [2895000000000]) (some (1, 9, 6)) (some (1, 9, 6)) (.next ([-1380000000000],
    [1635000000000]) (some (1, 9, 6)) (some (1, 9, 6)) (.next ([-2520000000000], [2895000000000])
    (some (1, 9, 6)) (some (1, 9, 6)) (.next ([-1357800000000, -4680000000000], [1496400000000,
    2340000000000]) (some (1, 9, 6)) (some (1, 9, 6)) (.terminal (some (1, 9, 6)) (some (1, 9, 6))
    (some (1, 9, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan9Owner0Part1 : FanWitness := (.next ([2265000000000], [630000000000]) (some (7, 2, 9)) (some
    (7, 2, 9)) (.next ([630000000000], [375000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next
    ([1515000000000], [1005000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next ([513600000000,
    -2340000000000], [352800000000, 4680000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next
    ([375000000000], [375000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next ([3402000000000],
    [3708000000000]) (some (7, 2, 9)) (some (8, 3, 9)) (.next ([4384800000000, 4680000000000],
    [5106600000000, -2340000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([4407000000000],
    [5223000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([866400000000, 2340000000000],
    [1121400000000, 2340000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([982800000000,
    4680000000000], [1398600000000, -2340000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next
    ([4032000000000], [5973000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([1005000000000],
    [1515000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([3777000000000], [6228000000000])
    (some (8, 3, 9)) (some (8, 3, 9)) (.next ([375000000000], [630000000000]) (some (8, 3, 9)) (some
    (8, 3, 9)) (.next ([3027000000000], [6603000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next
    ([2772000000000], [6603000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([2397000000000],
    [5973000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([2397000000000], [6228000000000])
    (some (8, 3, 9)) (some (8, 3, 9)) (.next ([630000000000], [2265000000000]) (some (8, 3, 9))
    (some (8, 9, 9)) (.next ([255000000000], [1380000000000]) (some (8, 9, 9)) (some (8, 9, 9))
    (.next ([375000000000], [2520000000000]) (some (8, 9, 9)) (some (8, 9, 9)) (.next
    ([138600000000, -2340000000000], [1357800000000, 4680000000000]) (some (8, 9, 9)) (some (8, 9,
    9)) (.next ([0], [1380000000000]) (some (8, 9, 9)) (some (8, 9, 9)) (.next ([-116400000000,
    -2340000000000], [1612800000000, 4680000000000]) (some (0, 9, 9)) (some (0, 9, 9))
    fan9Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan12Owner0Part0 : FanWitness := (.next ([0], [1380000000000]) (some (9, 3, 9)) (some (9, 3, 9))
    (.next ([-116400000000, -2340000000000], [1612800000000, 4680000000000]) (some (9, 3, 9)) (some
    (9, 4, 9)) (.next ([-375000000000], [2895000000000]) (some (9, 4, 9)) (some (9, 4, 9)) (.next
    ([-255000000000], [1635000000000]) (some (9, 4, 9)) (some (9, 4, 9)) (.next ([-630000000000],
    [2895000000000]) (some (9, 4, 9)) (some (9, 4, 9)) (.next ([-3105000000000], [8625000000000])
    (some (9, 4, 9)) (some (9, 4, 9)) (.next ([-3105000000000], [8370000000000]) (some (0, 4, 9))
    (some (0, 4, 9)) (.next ([-3480000000000], [9375000000000]) (some (0, 4, 9)) (some (0, 4, 9))
    (.next ([-375000000000], [1005000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next
    ([-3735000000000], [9630000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-1005000000000],
    [2520000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-352800000000, -4680000000000],
    [866400000000, 2340000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-3618600000000,
    2340000000000], [8017200000000, -4680000000000]) (some (0, 4, 9)) (some (0, 5, 9)) (.next
    ([-4740000000000], [10005000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-375000000000],
    [750000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-607800000000, -4680000000000],
    [1121400000000, 2340000000000]) (some (0, 5, 9)) (some (1, 5, 9)) (.next ([-1398600000000,
    2340000000000], [2381400000000, 2340000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next
    ([-1515000000000], [2520000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-630000000000],
    [1005000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-6000000000000], [9000000000000])
    (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-2265000000000], [2895000000000]) (some (1, 5, 9))
    (some (1, 5, 9)) (.next ([-1380000000000], [1635000000000]) (some (1, 5, 9)) (some (1, 5, 9))
    (.next ([-2520000000000], [2895000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next
    ([-1357800000000, -4680000000000], [1496400000000, 2340000000000]) (some (1, 5, 9)) (some (1, 5,
    9)) (.terminal (some (1, 5, 9)) (some (1, 5, 9)) (some (1, 5, 9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner0Part0 : FanWitness := (.next ([-1005000000000], [7935000000000]) (some (0, 9, 5))
    (some (0, 9, 5)) (.next ([-375000000000], [2895000000000]) (some (0, 9, 5)) (some (0, 9, 5))
    (.next ([-1005000000000], [7680000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next
    ([-255000000000], [1635000000000]) (some (0, 9, 5)) (some (9, 9, 5)) (.next ([-630000000000],
    [2895000000000]) (some (9, 9, 5)) (some (9, 9, 5)) (.next ([-375000000000], [1005000000000])
    (some (9, 9, 5)) (some (9, 9, 5)) (.next ([-1005000000000], [2520000000000]) (some (9, 9, 5))
    (some (9, 9, 5)) (.next ([-870000000000], [2130000000000]) (some (9, 9, 5)) (some (9, 9, 5))
    (.next ([-1005000000000], [2265000000000]) (some (9, 9, 5)) (some (9, 9, 5)) (.next
    ([-120000000000], [255000000000]) (some (9, 9, 5)) (some (9, 9, 5)) (.next ([-495000000000],
    [1005000000000]) (some (9, 9, 5)) (some (9, 9, 5)) (.next ([-375000000000], [750000000000])
    (some (9, 9, 5)) (some (9, 9, 5)) (.next ([-1125000000000], [2130000000000]) (some (9, 9, 5))
    (some (9, 9, 5)) (.next ([-1260000000000], [2385000000000]) (some (9, 9, 5)) (some (9, 9, 5))
    (.next ([-750000000000], [1260000000000]) (some (9, 9, 5)) (some (9, 9, 6)) (.next
    ([-1515000000000], [2520000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next ([-630000000000],
    [1005000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next ([-2265000000000], [2895000000000])
    (some (9, 9, 6)) (some (9, 9, 6)) (.next ([-7305000000000], [9195000000000]) (some (9, 9, 6))
    (some (9, 9, 6)) (.next ([-1380000000000], [1635000000000]) (some (9, 5, 6)) (some (9, 5, 6))
    (.next ([-2520000000000], [2895000000000]) (some (9, 5, 6)) (some (9, 5, 6)) (.next
    ([-6300000000000], [6930000000000]) (some (9, 5, 6)) (some (9, 5, 6)) (.next ([-1500000000000],
    [1635000000000]) (some (9, 5, 6)) (some (9, 5, 6)) (.next ([-6300000000000], [6675000000000])
    (some (9, 5, 6)) (some (9, 5, 6)) (.terminal (some (9, 5, 6)) (some (9, 5, 6)) (some (9, 5,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner0Part1 : FanWitness := (.next ([1515000000000], [1005000000000]) (some (6, 9, 5))
    (some (6, 9, 5)) (.next ([1260000000000], [870000000000]) (some (6, 9, 5)) (some (6, 9, 5))
    (.next ([1260000000000], [1005000000000]) (some (6, 9, 5)) (some (6, 9, 5)) (.next
    ([135000000000], [120000000000]) (some (6, 9, 5)) (some (6, 9, 5)) (.next ([510000000000],
    [495000000000]) (some (6, 9, 5)) (some (7, 9, 5)) (.next ([375000000000], [375000000000]) (some
    (7, 9, 5)) (some (7, 9, 5)) (.next ([1005000000000], [1125000000000]) (some (7, 9, 5)) (some (8,
    9, 5)) (.next ([1125000000000], [1260000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next
    ([510000000000], [750000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([1005000000000],
    [1515000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([375000000000], [630000000000]) (some
    (8, 9, 5)) (some (8, 9, 5)) (.next ([630000000000], [2265000000000]) (some (8, 9, 5)) (some (8,
    9, 5)) (.next ([1890000000000], [7305000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next
    ([255000000000], [1380000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([375000000000],
    [2520000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([630000000000], [6300000000000])
    (some (8, 9, 5)) (some (8, 9, 5)) (.next ([135000000000], [1500000000000]) (some (8, 9, 5))
    (some (8, 9, 5)) (.next ([375000000000], [6300000000000]) (some (8, 9, 5)) (some (8, 9, 5))
    (.next ([0], [1380000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([-375000000000],
    [6675000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next ([-495000000000], [8430000000000])
    (some (0, 9, 5)) (some (0, 9, 5)) (.next ([-120000000000], [1755000000000]) (some (0, 9, 5))
    (some (0, 9, 5)) (.next ([-630000000000], [8310000000000]) (some (0, 9, 5)) (some (0, 9, 5))
    (.next ([-630000000000], [6930000000000]) (some (0, 9, 5)) (some (0, 9, 5))
    fan14Owner0Part0))))))))))))))))))))))))

theorem excluded8_0 : ExcludedOn (model8.B 0 ++ [step8.q]) 9000000000000 (model8.caps 0) (model8.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1496400000000, 2340000000000], [116400000000,
      2340000000000]) (some (9, 1, 9)) (some (9, 2, 9)) (.next ([2520000000000], [375000000000])
      (some (9, 2, 9)) (some (9, 2, 9)) (.next ([1380000000000], [255000000000]) (some (9, 2, 9))
      (some (9, 2, 9)) fan8Owner0Part1)))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_1 : ExcludedOn (model8.B 1 ++ [step8.q]) 9000000000000 (model8.caps 1) (model8.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([570000000000, -9000000000000], [375000000000,
      0]) none none (.next ([1890000000000, 9000000000000], [1890000000000, 9000000000000]) none
      none (.next ([1890000000000, 9000000000000], [2610000000000, -9000000000000]) none none (.next
      ([1515000000000, 9000000000000], [2835000000000]) none none (.next ([0], [6390000000000,
      9000000000000]) none none (.next ([-375000000000, 0], [945000000000, -9000000000000]) (some
      (3, 1, 2)) none (.next ([-1890000000000, -9000000000000], [3780000000000, 18000000000000])
      none none (.next ([-2610000000000, 9000000000000], [4500000000000, 0]) none none (.next
      ([-2835000000000], [4350000000000, 9000000000000]) none none (.terminal none none
      none))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([570000000000, -9000000000000], [375000000000,
      0]) (some (2, 4, 1)) (some (3, 4, 2)) (.next ([2835000000000], [4650000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2835000000000], [6540000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1890000000000, 9000000000000], [5220000000000,
      -18000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1890000000000, 9000000000000],
      [7110000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([945000000000,
      -9000000000000], [6540000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [7110000000000, -9000000000000]) (some (3, 0, 2)) (some (4, 0, 2)) (.next ([-375000000000, 0],
      [945000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-4650000000000,
      9000000000000], [7485000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([-6540000000000], [9375000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-5220000000000,
      18000000000000], [7110000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([-7110000000000, 9000000000000], [9000000000000, 0]) (some (4, 0, 2)) (some (4, 1, 2)) (.next
      ([-6540000000000, 0], [7485000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.terminal (some (4, 1, 2)) (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([1496400000000, 2340000000000], [116400000000,
      2340000000000]) (some (6, 1, 9)) (some (7, 2, 9)) (.next ([2520000000000], [375000000000])
      (some (7, 2, 9)) (some (7, 2, 9)) (.next ([1380000000000], [255000000000]) (some (7, 2, 9))
      (some (7, 2, 9)) fan9Owner0Part1)))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_1 : ExcludedOn (model9.B 1 ++ [step9.q]) 9000000000000 (model9.caps 1) (model9.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3402000000000, 0], [1890000000000,
      9000000000000]) none none (.next ([1890000000000, 9000000000000], [1890000000000,
      9000000000000]) (some (2, 3, 2)) (some (2, 3, 2)) (.next ([1890000000000, 9000000000000],
      [2610000000000, -9000000000000]) (some (2, 3, 2)) (some (2, 3, 2)) (.next ([0],
      [6390000000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-1890000000000,
      -9000000000000], [5292000000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next
      ([-1890000000000, -9000000000000], [3780000000000, 18000000000000]) (some (0, 3, 2)) (some (3,
      3, 2)) (.next ([-2610000000000, 9000000000000], [4500000000000, 0]) (some (3, 3, 2)) (some (3,
      3, 2)) (.terminal (some (3, 3, 2)) none none))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_2 : ExcludedOn (model9.B 2 ++ [step9.q]) 9000000000000 (model9.caps 2) (model9.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_7 : ExcludedOn (model9.B 7 ++ [step9.q]) 9000000000000 (model9.caps 7) (model9.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded9_0
    · exact excluded9_1
    · exact excluded9_2
    · exact excluded9_3
    · exact excluded9_4
    · exact excluded9_5
    · exact (hj rfl).elim
    · exact excluded9_7
    · exact excluded9_8
    · exact excluded9_9
theorem next9 : model9.insert step9 = model10 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded10_0 : ExcludedOn (model10.B 0 ++ [step10.q]) 9000000000000 (model10.caps 0)
    (model10.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_2 : ExcludedOn (model10.B 2 ++ [step10.q]) 9000000000000 (model10.caps 2)
    (model10.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_7 : ExcludedOn (model10.B 7 ++ [step10.q]) 9000000000000 (model10.caps 7)
    (model10.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2385000000000, -9000000000000], [1890000000000,
      9000000000000]) (some (2, 0, 1)) (some (3, 0, 2)) (.next ([1890000000000, 9000000000000],
      [2835000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1890000000000,
      9000000000000], [5220000000000, -18000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([1890000000000, 9000000000000], [7110000000000, -9000000000000]) (some (3, 0, 2)) (some (3,
      0, 2)) (.next ([0, 0], [7110000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2))
      (.next ([-1890000000000, -9000000000000], [4275000000000]) (some (0, 0, 2)) (some (0, 0, 2))
      (.next ([-2835000000000, 9000000000000], [4725000000000, 0]) (some (0, 0, 2)) (some (0, 0, 2))
      (.next ([-5220000000000, 18000000000000], [7110000000000, -9000000000000]) (some (0, 0, 2))
      (some (0, 4, 2)) (.next ([-7110000000000, 9000000000000], [9000000000000, 0]) (some (0, 4, 2))
      (some (0, 4, 2)) (.terminal (some (0, 4, 2)) (some (0, 1, 2)) (some (0, 4, 2))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_1 : ExcludedOn (model11.B 1 ++ [step11.q]) 9000000000000 (model11.caps 1)
    (model11.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1890000000000, 9000000000000], [1890000000000,
      9000000000000]) none none (.next ([1890000000000, 9000000000000], [2835000000000,
      -9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([1890000000000, 9000000000000],
      [4200000000000, -9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([0],
      [6615000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1890000000000,
      -9000000000000], [3780000000000, 18000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-2835000000000, 9000000000000], [4725000000000, 0]) (some (0, 1, 3)) (some (1, 1, 3)) (.next
      ([-4200000000000, 9000000000000], [6090000000000, 0]) (some (1, 1, 3)) (some (1, 1, 3))
      (.terminal (some (1, 1, 3)) none none))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded11_5
    · exact excluded11_6
    · exact (hj rfl).elim
    · exact excluded11_8
    · exact excluded11_9
theorem next11 : model11.insert step11 = model12 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded12_0 : ExcludedOn (model12.B 0 ++ [step12.q]) 9000000000000 (model12.caps 0)
    (model12.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1496400000000, 2340000000000], [116400000000,
      2340000000000]) (some (9, 1, 5)) (some (9, 2, 5)) (.next ([2520000000000], [375000000000])
      (some (9, 2, 5)) (some (9, 2, 5)) (.next ([1380000000000], [255000000000]) (some (9, 2, 5))
      (some (9, 2, 5)) (.next ([2265000000000], [630000000000]) (some (9, 2, 5)) (some (9, 2, 5))
      (.next ([5520000000000], [3105000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next
      ([5265000000000], [3105000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next ([5895000000000],
      [3480000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next ([630000000000], [375000000000])
      (some (9, 2, 5)) (some (9, 2, 5)) (.next ([5895000000000], [3735000000000]) (some (9, 2, 5))
      (some (9, 2, 5)) (.next ([1515000000000], [1005000000000]) (some (9, 2, 5)) (some (9, 2, 5))
      (.next ([513600000000, -2340000000000], [352800000000, 4680000000000]) (some (9, 2, 5)) (some
      (9, 2, 5)) (.next ([4398600000000, -2340000000000], [3618600000000, -2340000000000]) (some (9,
      2, 5)) (some (9, 2, 5)) (.next ([5265000000000], [4740000000000]) (some (9, 2, 5)) (some (9,
      2, 5)) (.next ([375000000000], [375000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next
      ([513600000000, -2340000000000], [607800000000, 4680000000000]) (some (9, 2, 5)) (some (9, 3,
      5)) (.next ([982800000000, 4680000000000], [1398600000000, -2340000000000]) (some (9, 3, 5))
      (some (9, 3, 5)) (.next ([1005000000000], [1515000000000]) (some (9, 3, 5)) (some (9, 3, 5))
      (.next ([375000000000], [630000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
      ([3000000000000], [6000000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([630000000000],
      [2265000000000]) (some (9, 3, 5)) (some (9, 3, 9)) (.next ([255000000000], [1380000000000])
      (some (9, 3, 9)) (some (9, 3, 9)) (.next ([375000000000], [2520000000000]) (some (9, 3, 9))
      (some (9, 3, 9)) (.next ([138600000000, -2340000000000], [1357800000000, 4680000000000]) (some
      (9, 3, 9)) (some (9, 3, 9)) fan12Owner0Part0)))))))))))))))))))))))) (den := 9000000000000)
      (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded12_1 : ExcludedOn (model12.B 1 ++ [step12.q]) 9000000000000 (model12.caps 1)
    (model12.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_2 : ExcludedOn (model12.B 2 ++ [step12.q]) 9000000000000 (model12.caps 2)
    (model12.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded12_7 : ExcludedOn (model12.B 7 ++ [step12.q]) 9000000000000 (model12.caps 7)
    (model12.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded12_4
    · exact excluded12_5
    · exact excluded12_6
    · exact excluded12_7
    · exact excluded12_8
    · exact excluded12_9
theorem next12 : model12.insert step12 = model13 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded13_1 : ExcludedOn (model13.B 1 ++ [step13.q]) 9000000000000 (model13.caps 1)
    (model13.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_2 : ExcludedOn (model13.B 2 ++ [step13.q]) 9000000000000 (model13.caps 2)
    (model13.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7605000000000, -9000000000000], [765000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([6660000000000], [1335000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([6480000000000, -9000000000000], [1395000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([6540000000000, 0], [1515000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7110000000000, -9000000000000],
      [1890000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([570000000000,
      -9000000000000], [375000000000, 0]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([1890000000000,
      9000000000000], [1890000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next
      ([2385000000000, 9000000000000], [5985000000000, -9000000000000]) (some (0, 4, 1)) (some (0,
      4, 1)) (.next ([375000000000, 0], [4275000000000, -9000000000000]) (some (0, 4, 1)) (some (0,
      4, 1)) (.next ([495000000000], [7875000000000]) (some (0, 4, 1)) (some (0, 4, 2)) (.next
      ([375000000000], [6165000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0],
      [1890000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-765000000000,
      -9000000000000], [8370000000000, 0]) (some (0, 4, 2)) (some (0, 4, 3)) (.next
      ([-1335000000000], [7995000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1395000000000,
      -9000000000000], [7875000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1515000000000,
      -9000000000000], [8055000000000, 9000000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.next
      ([-1890000000000, -9000000000000], [9000000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([-375000000000, 0], [945000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([-1890000000000, -9000000000000], [3780000000000, 18000000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([-5985000000000, 9000000000000], [8370000000000, 0]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([-4275000000000, 9000000000000], [4650000000000, -9000000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-7875000000000], [8370000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([-6165000000000], [6540000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.terminal (some (4, 1, 3)) (some (4, 1, 0)) (some (4, 1, 3))))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_3 : ExcludedOn (model13.B 3 ++ [step13.q]) 9000000000000 (model13.caps 3)
    (model13.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7875000000000], [630000000000]) (some (1, 0, 3))
      (some (2, 0, 3)) (.next ([4890000000000], [1890000000000, 9000000000000]) (some (2, 0, 3))
      (some (2, 0, 3)) (.next ([5985000000000, -9000000000000], [2520000000000, 9000000000000])
      (some (2, 0, 3)) (some (2, 0, 3)) (.next ([4260000000000], [3615000000000]) (some (2, 0, 3))
      (some (2, 3, 3)) (.next ([0], [1890000000000, 9000000000000]) (some (2, 3, 1)) (some (2, 3,
      1)) (.next ([-630000000000], [8505000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([-1890000000000, -9000000000000], [6780000000000, 9000000000000]) (some (0, 3, 1)) (some (0,
      3, 1)) (.next ([-2520000000000, -9000000000000], [8505000000000]) (some (0, 3, 1)) (some (0,
      3, 1)) (.next ([-3615000000000], [7875000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.terminal
      (some (0, 3, 1)) (some (0, 3, 1)) (some (0, 3, 1))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_4 : ExcludedOn (model13.B 4 ++ [step13.q]) 9000000000000 (model13.caps 4)
    (model13.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_5 : ExcludedOn (model13.B 5 ++ [step13.q]) 9000000000000 (model13.caps 5)
    (model13.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6300000000000], [375000000000]) (some (6, 9, 5))
      (some (6, 9, 5)) (.next ([7935000000000], [495000000000]) (some (6, 9, 5)) (some (6, 9, 5))
      (.next ([1635000000000], [120000000000]) (some (6, 9, 5)) (some (6, 9, 5)) (.next
      ([7680000000000], [630000000000]) (some (6, 9, 5)) (some (6, 9, 5)) (.next ([6300000000000],
      [630000000000]) (some (6, 9, 5)) (some (6, 9, 5)) (.next ([6930000000000], [1005000000000])
      (some (6, 9, 5)) (some (6, 9, 5)) (.next ([2520000000000], [375000000000]) (some (6, 9, 5))
      (some (6, 9, 5)) (.next ([6675000000000], [1005000000000]) (some (6, 9, 5)) (some (6, 9, 5))
      (.next ([1380000000000], [255000000000]) (some (6, 9, 5)) (some (6, 9, 5)) (.next
      ([2265000000000], [630000000000]) (some (6, 9, 5)) (some (6, 9, 5)) (.next ([630000000000],
      [375000000000]) (some (6, 9, 5)) (some (6, 9, 5)) fan14Owner0Part1)))))))))))) (den :=
      9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded14_1 : ExcludedOn (model14.B 1 ++ [step14.q]) 9000000000000 (model14.caps 1)
    (model14.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_2 : ExcludedOn (model14.B 2 ++ [step14.q]) 9000000000000 (model14.caps 2)
    (model14.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_3 : ExcludedOn (model14.B 3 ++ [step14.q]) 9000000000000 (model14.caps 3)
    (model14.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_4 : ExcludedOn (model14.B 4 ++ [step14.q]) 9000000000000 (model14.caps 4)
    (model14.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_6 : ExcludedOn (model14.B 6 ++ [step14.q]) 9000000000000 (model14.caps 6)
    (model14.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_7 : ExcludedOn (model14.B 7 ++ [step14.q]) 9000000000000 (model14.caps 7)
    (model14.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_8 : ExcludedOn (model14.B 8 ++ [step14.q]) 9000000000000 (model14.caps 8)
    (model14.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_9 : ExcludedOn (model14.B 9 ++ [step14.q]) 9000000000000 (model14.caps 9)
    (model14.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded14_4
    · exact (hj rfl).elim
    · exact excluded14_6
    · exact excluded14_7
    · exact excluded14_8
    · exact excluded14_9
theorem next14 : model14.insert step14 = model15 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded15_1 : ExcludedOn (model15.B 1 ++ [step15.q]) 9000000000000 (model15.caps 1)
    (model15.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_2 : ExcludedOn (model15.B 2 ++ [step15.q]) 9000000000000 (model15.caps 2)
    (model15.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7110000000000, -9000000000000], [615000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([6165000000000], [1185000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([6540000000000, 0], [1515000000000, 9000000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7110000000000, -9000000000000], [1890000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([5835000000000, -9000000000000],
      [1890000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([570000000000,
      -9000000000000], [375000000000, 0]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([1890000000000,
      9000000000000], [1890000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next
      ([1890000000000, 9000000000000], [5835000000000, -9000000000000]) (some (0, 4, 1)) (some (0,
      4, 1)) (.next ([375000000000, 0], [4275000000000, -9000000000000]) (some (0, 4, 1)) (some (0,
      4, 1)) (.next ([375000000000], [6165000000000]) (some (0, 4, 1)) (some (0, 4, 2)) (.next ([0,
      0], [1890000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-615000000000,
      -9000000000000], [7725000000000, 0]) (some (0, 4, 2)) (some (0, 4, 3)) (.next
      ([-1185000000000], [7350000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1515000000000,
      -9000000000000], [8055000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1890000000000, -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-1890000000000, -9000000000000], [7725000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-375000000000, 0], [945000000000, -9000000000000]) (some (0, 1, 3)) (some (4, 1, 3))
      (.next ([-1890000000000, -9000000000000], [3780000000000, 18000000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([-5835000000000, 9000000000000], [7725000000000, 0]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([-4275000000000, 9000000000000], [4650000000000, -9000000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-6165000000000], [6540000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.terminal (some (4, 1, 3)) (some (4, 1, 0)) (some (4, 1,
      3))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded15_3 : ExcludedOn (model15.B 3 ++ [step15.q]) 9000000000000 (model15.caps 3)
    (model15.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7725000000000], [1275000000000]) (some (1, 0,
      3)) (some (2, 0, 3)) (.next ([4890000000000], [1890000000000, 9000000000000]) (some (2, 0, 3))
      (some (2, 0, 3)) (.next ([5835000000000, -9000000000000], [3165000000000, 9000000000000])
      (some (2, 0, 3)) (some (2, 0, 3)) (.next ([3615000000000], [4110000000000]) (some (2, 0, 3))
      (some (2, 3, 3)) (.next ([0], [1890000000000, 9000000000000]) (some (2, 3, 1)) (some (2, 3,
      1)) (.next ([-1275000000000], [9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([-1890000000000, -9000000000000], [6780000000000, 9000000000000]) (some (0, 3, 1)) (some (0,
      3, 1)) (.next ([-3165000000000, -9000000000000], [9000000000000]) (some (0, 3, 1)) (some (0,
      3, 1)) (.next ([-4110000000000], [7725000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.terminal
      (some (0, 3, 1)) (some (0, 3, 1)) (some (0, 3, 1))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded15_4 : ExcludedOn (model15.B 4 ++ [step15.q]) 9000000000000 (model15.caps 4)
    (model15.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_5 : ExcludedOn (model15.B 5 ++ [step15.q]) 9000000000000 (model15.caps 5)
    (model15.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_6 : ExcludedOn (model15.B 6 ++ [step15.q]) 9000000000000 (model15.caps 6)
    (model15.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_7 : ExcludedOn (model15.B 7 ++ [step15.q]) 9000000000000 (model15.caps 7)
    (model15.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded15_1
    · exact excluded15_2
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

end Aown210000220000
end ConwaySoifer.Simplified.Certificates
