/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown170000180000
import Mathlib.Tactic.FinCases

/-!
# Aown 170000 180000 2

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
namespace Aown170000180000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part0 : FanWitness := (.next ([-1245000000000], [5010000000000]) (some (0, 4, 9))
    (some (0, 4, 9)) (.next ([-2610000000000], [7470000000000]) (some (0, 4, 9)) (some (0, 4, 9))
    (.next ([-1995000000000], [5385000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next
    ([-3630000000000], [9375000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-2130000000000],
    [5385000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-3765000000000], [9510000000000])
    (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-375000000000], [885000000000]) (some (0, 4, 9))
    (some (0, 4, 9)) (.next ([-885000000000], [2040000000000]) (some (0, 4, 9)) (some (0, 4, 9))
    (.next ([-4515000000000], [9885000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next
    ([-885000000000], [1905000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-4650000000000],
    [9885000000000]) (some (0, 4, 9)) (some (0, 5, 9)) (.next ([-375000000000], [750000000000])
    (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-2505000000000], [4875000000000]) (some (0, 5, 9))
    (some (1, 5, 9)) (.next ([-5025000000000], [9510000000000]) (some (1, 5, 9)) (some (1, 5, 9))
    (.next ([-1020000000000], [1905000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next
    ([-5025000000000], [9375000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-1620000000000],
    [2970000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-4140000000000], [7470000000000])
    (some (1, 5, 9)) (some (1, 6, 9)) (.next ([-2520000000000], [4500000000000]) (some (1, 6, 9))
    (some (1, 6, 9)) (.next ([-1155000000000], [2040000000000]) (some (1, 6, 9)) (some (1, 9, 9))
    (.next ([-510000000000], [885000000000]) (some (1, 9, 9)) (some (1, 9, 9)) (.next
    ([-1905000000000], [2415000000000]) (some (1, 9, 9)) (some (1, 9, 9)) (.next ([-2040000000000],
    [2415000000000]) (some (1, 9, 9)) (some (1, 9, 9)) (.next ([-1260000000000], [1395000000000])
    (some (1, 9, 9)) (some (1, 9, 9)) (.terminal (some (1, 9, 9)) (some (1, 9, 9)) (some (1, 9,
    9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part1 : FanWitness := (.next ([510000000000], [375000000000]) (some (7, 2, 9)) (some
    (7, 2, 9)) (.next ([1155000000000], [885000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next
    ([5370000000000], [4515000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next ([1020000000000],
    [885000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next ([5235000000000], [4650000000000])
    (some (7, 2, 9)) (some (7, 2, 9)) (.next ([375000000000], [375000000000]) (some (7, 2, 9)) (some
    (7, 2, 9)) (.next ([2370000000000], [2505000000000]) (some (7, 2, 9)) (some (7, 3, 9)) (.next
    ([4485000000000], [5025000000000]) (some (7, 3, 9)) (some (7, 3, 9)) (.next ([885000000000],
    [1020000000000]) (some (7, 3, 9)) (some (7, 3, 9)) (.next ([4350000000000], [5025000000000])
    (some (7, 3, 9)) (some (8, 3, 9)) (.next ([1350000000000], [1620000000000]) (some (8, 3, 9))
    (some (8, 3, 9)) (.next ([3330000000000], [4140000000000]) (some (8, 3, 9)) (some (8, 3, 9))
    (.next ([1980000000000], [2520000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next
    ([885000000000], [1155000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([375000000000],
    [510000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([510000000000], [1905000000000]) (some
    (8, 3, 9)) (some (8, 3, 9)) (.next ([375000000000], [2040000000000]) (some (8, 3, 9)) (some (8,
    3, 9)) (.next ([135000000000], [1260000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([0],
    [1260000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([-90000000000], [2970000000000])
    (some (0, 3, 9)) (some (0, 4, 9)) (.next ([-135000000000], [1395000000000]) (some (0, 4, 9))
    (some (0, 4, 9)) (.next ([-375000000000], [2415000000000]) (some (0, 4, 9)) (some (0, 4, 9))
    (.next ([-510000000000], [2415000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next
    ([-1110000000000], [4875000000000]) (some (0, 4, 9)) (some (0, 4, 9))
    fan18Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part0 : FanWitness := (.next ([-1905000000000], [7290000000000]) (some (0, 4, 9))
    (some (0, 4, 9)) (.next ([-2619000000000], [9375000000000]) (some (0, 4, 9)) (some (0, 4, 9))
    (.next ([-2040000000000], [7290000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next
    ([-2754000000000], [9510000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-1509000000000],
    [4500000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-2415000000000], [6915000000000])
    (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-3504000000000], [9885000000000]) (some (0, 4, 9))
    (some (0, 4, 9)) (.next ([-2415000000000], [6780000000000]) (some (0, 4, 9)) (some (0, 4, 9))
    (.next ([-3639000000000], [9885000000000]) (some (0, 4, 9)) (some (0, 5, 9)) (.next
    ([-1995000000000], [5385000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-2130000000000],
    [5385000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-4014000000000], [9510000000000])
    (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-375000000000], [885000000000]) (some (0, 5, 9))
    (some (0, 5, 9)) (.next ([-4014000000000], [9375000000000]) (some (0, 5, 9)) (some (0, 5, 9))
    (.next ([-375000000000], [750000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next
    ([-2505000000000], [4875000000000]) (some (0, 5, 9)) (some (1, 5, 9)) (.next ([-1020000000000],
    [1905000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-1155000000000], [2040000000000])
    (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-510000000000], [885000000000]) (some (1, 5, 9))
    (some (1, 5, 9)) (.next ([-1599000000000], [2595000000000]) (some (1, 5, 9)) (some (1, 5, 9))
    (.next ([-1905000000000], [2415000000000]) (some (1, 5, 9)) (some (1, 9, 9)) (.next
    ([-2040000000000], [2415000000000]) (some (1, 9, 9)) (some (1, 9, 9)) (.next ([-1260000000000],
    [1395000000000]) (some (1, 9, 9)) (some (1, 9, 9)) (.next ([-1905000000000], [1995000000000])
    (some (1, 9, 9)) (some (1, 9, 9)) (.terminal (some (1, 9, 9)) (some (1, 9, 9)) (some (1, 9,
    9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part1 : FanWitness := (.next ([3255000000000], [2130000000000]) (some (7, 2, 9))
    (some (7, 2, 9)) (.next ([5496000000000], [4014000000000]) (some (7, 2, 9)) (some (7, 2, 9))
    (.next ([510000000000], [375000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next
    ([5361000000000], [4014000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next ([375000000000],
    [375000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next ([2370000000000], [2505000000000])
    (some (7, 2, 9)) (some (7, 3, 9)) (.next ([885000000000], [1020000000000]) (some (7, 3, 9))
    (some (7, 3, 9)) (.next ([885000000000], [1155000000000]) (some (7, 3, 9)) (some (8, 3, 9))
    (.next ([375000000000], [510000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next
    ([996000000000], [1599000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([510000000000],
    [1905000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([375000000000], [2040000000000])
    (some (8, 3, 9)) (some (8, 3, 9)) (.next ([135000000000], [1260000000000]) (some (8, 3, 9))
    (some (8, 3, 9)) (.next ([90000000000], [1905000000000]) (some (8, 3, 9)) (some (8, 3, 9))
    (.next ([0], [1260000000000]) (some (8, 3, 9)) (some (8, 3, 9)) (.next ([-90000000000],
    [2970000000000]) (some (0, 3, 9)) (some (0, 4, 9)) (.next ([-135000000000], [1395000000000])
    (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-1020000000000], [6780000000000]) (some (0, 4, 9))
    (some (0, 4, 9)) (.next ([-375000000000], [2415000000000]) (some (0, 4, 9)) (some (0, 4, 9))
    (.next ([-1155000000000], [6915000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next
    ([-510000000000], [2415000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-1599000000000],
    [7470000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-1110000000000], [4875000000000])
    (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-1245000000000], [5010000000000]) (some (0, 4, 9))
    (some (0, 4, 9)) fan20Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner0Part0 : FanWitness := (.next ([-2415000000000], [6780000000000]) (some (0, 5, 11))
    (some (0, 5, 11)) (.next ([-615000000000], [1725000000000]) (some (0, 5, 11)) (some (0, 5, 11))
    (.next ([-1995000000000], [5385000000000]) (some (0, 5, 11)) (some (0, 5, 11)) (.next
    ([-2130000000000], [5385000000000]) (some (0, 5, 11)) (some (0, 5, 11)) (.next ([-375000000000],
    [885000000000]) (some (0, 5, 11)) (some (0, 5, 11)) (.next ([-750000000000], [1740000000000])
    (some (0, 5, 11)) (some (0, 5, 11)) (.next ([-375000000000], [750000000000]) (some (0, 5, 11))
    (some (0, 11, 11)) (.next ([-2505000000000], [4875000000000]) (some (0, 11, 11)) (some (1, 11,
    11)) (.next ([-1020000000000], [1905000000000]) (some (1, 11, 11)) (some (1, 11, 11)) (.next
    ([-1155000000000], [2040000000000]) (some (1, 11, 11)) (some (1, 11, 11)) (.next
    ([-510000000000], [885000000000]) (some (1, 11, 11)) (some (1, 11, 11)) (.next
    ([-1995000000000], [3240000000000]) (some (1, 11, 11)) (some (1, 11, 11)) (.next
    ([-2010000000000], [3120000000000]) (some (1, 11, 11)) (some (1, 11, 11)) (.next
    ([-1905000000000], [2415000000000]) (some (1, 11, 11)) (some (1, 11, 11)) (.next
    ([-4965000000000], [6120000000000]) (some (1, 11, 11)) (some (1, 11, 11)) (.next
    ([-1830000000000], [2235000000000]) (some (1, 11, 11)) (some (1, 11, 11)) (.next
    ([-4980000000000], [6000000000000]) (some (1, 11, 7)) (some (1, 11, 7)) (.next
    ([-2040000000000], [2415000000000]) (some (1, 11, 7)) (some (1, 11, 7)) (.next
    ([-3735000000000], [4230000000000]) (some (1, 11, 7)) (some (1, 11, 7)) (.next ([-120000000000],
    [135000000000]) (some (1, 11, 7)) (some (1, 11, 7)) (.next ([-1260000000000], [1395000000000])
    (some (1, 11, 7)) (some (1, 11, 7)) (.next ([-6705000000000], [7110000000000]) (some (1, 11, 7))
    (some (1, 11, 7)) (.next ([-1905000000000], [1995000000000]) (some (1, 11, 7)) (some (1, 11, 7))
    (.next ([-6870000000000], [7005000000000]) (some (1, 11, 7)) (some (1, 11, 8)) (.terminal (some
    (1, 11, 8)) (some (1, 11, 8)) (some (1, 11, 8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner0Part1 : FanWitness := (.next ([-750000000000], [8745000000000]) (some (0, 4, 11))
    (some (0, 4, 11)) (.next ([-105000000000], [1125000000000]) (some (0, 4, 11)) (some (0, 4, 11))
    (.next ([-135000000000], [1395000000000]) (some (0, 4, 11)) (some (0, 4, 11)) (.next
    ([-750000000000], [7380000000000]) (some (0, 4, 11)) (some (0, 4, 11)) (.next ([-885000000000],
    [7395000000000]) (some (0, 4, 11)) (some (0, 4, 11)) (.next ([-885000000000], [7380000000000])
    (some (0, 4, 11)) (some (0, 4, 11)) (.next ([-1020000000000], [7395000000000]) (some (0, 4, 11))
    (some (0, 4, 11)) (.next ([-1020000000000], [6780000000000]) (some (0, 4, 11)) (some (0, 4, 11))
    (.next ([-375000000000], [2415000000000]) (some (0, 4, 11)) (some (0, 4, 11)) (.next
    ([-1500000000000], [9120000000000]) (some (0, 4, 11)) (some (0, 4, 11)) (.next
    ([-1155000000000], [6915000000000]) (some (0, 4, 11)) (some (0, 4, 11)) (.next
    ([-1635000000000], [9120000000000]) (some (0, 4, 11)) (some (0, 4, 11)) (.next
    ([-1260000000000], [7005000000000]) (some (0, 4, 11)) (some (0, 4, 11)) (.next
    ([-1260000000000], [6870000000000]) (some (0, 4, 11)) (some (0, 4, 11)) (.next
    ([-1395000000000], [7020000000000]) (some (0, 4, 11)) (some (0, 5, 11)) (.next
    ([-1395000000000], [6885000000000]) (some (0, 5, 11)) (some (0, 5, 11)) (.next ([-510000000000],
    [2415000000000]) (some (0, 5, 11)) (some (0, 5, 11)) (.next ([-1110000000000], [4875000000000])
    (some (0, 5, 11)) (some (0, 5, 11)) (.next ([-2010000000000], [8745000000000]) (some (0, 5, 11))
    (some (0, 5, 11)) (.next ([-2010000000000], [8610000000000]) (some (0, 5, 11)) (some (0, 5, 11))
    (.next ([-1245000000000], [5010000000000]) (some (0, 5, 11)) (some (0, 5, 11)) (.next
    ([-1905000000000], [7290000000000]) (some (0, 5, 11)) (some (0, 5, 11)) (.next
    ([-2040000000000], [7290000000000]) (some (0, 5, 11)) (some (0, 5, 11)) (.next
    ([-2415000000000], [6915000000000]) (some (0, 5, 11)) (some (0, 5, 11))
    fan23Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner0Part2 : FanWitness := (.next ([990000000000], [750000000000]) (some (9, 2, 11)) (some
    (9, 2, 11)) (.next ([375000000000], [375000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
    ([2370000000000], [2505000000000]) (some (9, 2, 11)) (some (9, 3, 11)) (.next ([885000000000],
    [1020000000000]) (some (9, 3, 11)) (some (9, 3, 11)) (.next ([885000000000], [1155000000000])
    (some (9, 3, 11)) (some (10, 3, 11)) (.next ([375000000000], [510000000000]) (some (10, 3, 11))
    (some (10, 3, 11)) (.next ([1245000000000], [1995000000000]) (some (10, 3, 11)) (some (10, 3,
    11)) (.next ([1110000000000], [2010000000000]) (some (10, 3, 11)) (some (10, 3, 11)) (.next
    ([510000000000], [1905000000000]) (some (10, 3, 11)) (some (10, 3, 11)) (.next ([1155000000000],
    [4965000000000]) (some (10, 3, 11)) (some (10, 3, 11)) (.next ([405000000000], [1830000000000])
    (some (10, 3, 11)) (some (10, 3, 11)) (.next ([1020000000000], [4980000000000]) (some (10, 3,
    11)) (some (10, 3, 11)) (.next ([375000000000], [2040000000000]) (some (10, 3, 11)) (some (10,
    3, 11)) (.next ([495000000000], [3735000000000]) (some (10, 3, 11)) (some (10, 3, 11)) (.next
    ([15000000000], [120000000000]) (some (10, 3, 11)) (some (10, 3, 11)) (.next ([135000000000],
    [1260000000000]) (some (10, 3, 11)) (some (10, 3, 11)) (.next ([405000000000], [6705000000000])
    (some (10, 3, 11)) (some (10, 3, 11)) (.next ([90000000000], [1905000000000]) (some (10, 3, 11))
    (some (10, 3, 11)) (.next ([135000000000], [6870000000000]) (some (10, 3, 11)) (some (10, 3,
    11)) (.next ([0], [1260000000000]) (some (10, 3, 11)) (some (10, 3, 11)) (.next
    ([-135000000000], [7020000000000]) (some (0, 3, 11)) (some (0, 4, 11)) (.next ([-90000000000],
    [2970000000000]) (some (0, 4, 11)) (some (0, 4, 11)) (.next ([-615000000000], [8610000000000])
    (some (0, 4, 11)) (some (0, 4, 11)) (.next ([-90000000000], [1245000000000]) (some (0, 4, 11))
    (some (0, 4, 11)) fan23Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner0Part3 : FanWitness := (.next ([6495000000000], [885000000000]) (some (9, 2, 11))
    (some (9, 2, 11)) (.next ([6375000000000], [1020000000000]) (some (9, 2, 11)) (some (9, 2, 11))
    (.next ([5760000000000], [1020000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
    ([2040000000000], [375000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([7620000000000],
    [1500000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([5760000000000], [1155000000000])
    (some (9, 2, 11)) (some (9, 2, 11)) (.next ([7485000000000], [1635000000000]) (some (9, 2, 11))
    (some (9, 2, 11)) (.next ([5745000000000], [1260000000000]) (some (9, 2, 11)) (some (9, 2, 11))
    (.next ([5610000000000], [1260000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
    ([5625000000000], [1395000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([5490000000000],
    [1395000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([1905000000000], [510000000000])
    (some (9, 2, 11)) (some (9, 2, 11)) (.next ([3765000000000], [1110000000000]) (some (9, 2, 11))
    (some (9, 2, 11)) (.next ([6735000000000], [2010000000000]) (some (9, 2, 11)) (some (9, 2, 11))
    (.next ([6600000000000], [2010000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
    ([3765000000000], [1245000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([5385000000000],
    [1905000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([5250000000000], [2040000000000])
    (some (9, 2, 11)) (some (9, 2, 11)) (.next ([4500000000000], [2415000000000]) (some (9, 2, 11))
    (some (9, 2, 11)) (.next ([4365000000000], [2415000000000]) (some (9, 2, 11)) (some (9, 2, 11))
    (.next ([1110000000000], [615000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
    ([3390000000000], [1995000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([3255000000000],
    [2130000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([510000000000], [375000000000])
    (some (9, 2, 11)) (some (9, 2, 11)) fan23Owner0Part2))))))))))))))))))))))))

theorem excluded16_0 : ExcludedOn (model16.B 0 ++ [step16.q]) 9000000000000 (model16.caps 0)
    (model16.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_4 : ExcludedOn (model16.B 4 ++ [step16.q]) 9000000000000 (model16.caps 4)
    (model16.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_6 : ExcludedOn (model16.B 6 ++ [step16.q]) 9000000000000 (model16.caps 6)
    (model16.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_7 : ExcludedOn (model16.B 7 ++ [step16.q]) 9000000000000 (model16.caps 7)
    (model16.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_8 : ExcludedOn (model16.B 8 ++ [step16.q]) 9000000000000 (model16.caps 8)
    (model16.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_9 : ExcludedOn (model16.B 9 ++ [step16.q]) 9000000000000 (model16.caps 9)
    (model16.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2250000000000, 0], [5985000000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 1, 2)) (.next ([2250000000000], [7515000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([720000000000, -9000000000000], [7515000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [1530000000000, 9000000000000]) (some (3, 1,
      2)) (some (3, 1, 3)) (.next ([-5985000000000, 9000000000000], [8235000000000, -9000000000000])
      (some (3, 1, 3)) (some (3, 1, 3)) (.next ([-7515000000000], [9765000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-7515000000000], [8235000000000, -9000000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.terminal (some (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded16_4
    · exact (hj rfl).elim
    · exact excluded16_6
    · exact excluded16_7
    · exact excluded16_8
    · exact excluded16_9
theorem next16 : model16.insert step16 = model17 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded17_1 : ExcludedOn (model17.B 1 ++ [step17.q]) 9000000000000 (model17.caps 1)
    (model17.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6120000000000], [3120000000000]) (some (2, 3,
      1)) none (.next ([3150000000000, 9000000000000], [2970000000000, -9000000000000]) none none
      (.next ([1530000000000, 9000000000000], [1530000000000, 9000000000000]) none none (.next
      ([1530000000000, 9000000000000], [3210000000000, -9000000000000]) none none (.next
      ([90000000000, -9000000000000], [4500000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([0], [6270000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-3120000000000], [9240000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2970000000000,
      9000000000000], [6120000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1530000000000,
      -9000000000000], [3060000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-3210000000000, 9000000000000], [4740000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-4500000000000, 0], [4590000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.terminal (some (3, 1, 2)) (some (3, 1, 2)) (some (3, 1, 2))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded17_2 : ExcludedOn (model17.B 2 ++ [step17.q]) 9000000000000 (model17.caps 2)
    (model17.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7500000000000, 0], [1020000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7470000000000, -9000000000000],
      [1530000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([3240000000000, 0],
      [1530000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([4500000000000],
      [2880000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([2970000000000, -9000000000000],
      [4410000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([510000000000],
      [3750000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([360000000000], [4140000000000])
      (some (0, 4, 1)) (some (0, 4, 2)) (.next ([510000000000], [6990000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([120000000000], [3990000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([90000000000, -9000000000000], [4500000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([0, 0], [1530000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-1020000000000, -9000000000000], [8520000000000, 9000000000000]) (some (0, 1, 2)) (some (0,
      1, 3)) (.next ([-1530000000000, -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some
      (0, 1, 3)) (.next ([-1530000000000, -9000000000000], [4770000000000, 9000000000000]) (some (0,
      1, 3)) (some (0, 1, 3)) (.next ([-2880000000000], [7380000000000]) (some (0, 1, 3)) (some (0,
      1, 3)) (.next ([-4410000000000, -9000000000000], [7380000000000]) (some (0, 1, 3)) (some (0,
      1, 3)) (.next ([-3750000000000], [4260000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.next
      ([-4140000000000], [4500000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-6990000000000], [7500000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-3990000000000], [4110000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-4500000000000,
      0], [4590000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1,
      3)) (some (4, 1, 0)) (some (4, 1, 3))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded17_3 : ExcludedOn (model17.B 3 ++ [step17.q]) 9000000000000 (model17.caps 3)
    (model17.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_4 : ExcludedOn (model17.B 4 ++ [step17.q]) 9000000000000 (model17.caps 4)
    (model17.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_8 : ExcludedOn (model17.B 8 ++ [step17.q]) 9000000000000 (model17.caps 8)
    (model17.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded17_1
    · exact excluded17_2
    · exact excluded17_3
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
  apply ExclusionHint.sound (.witnessedFan (.next ([2880000000000], [90000000000]) (some (9, 1, 9))
      (some (9, 2, 9)) (.next ([1260000000000], [135000000000]) (some (9, 2, 9)) (some (9, 2, 9))
      (.next ([2040000000000], [375000000000]) (some (9, 2, 9)) (some (9, 2, 9)) (.next
      ([1905000000000], [510000000000]) (some (9, 2, 9)) (some (9, 2, 9)) (.next ([3765000000000],
      [1110000000000]) (some (9, 2, 9)) (some (9, 2, 9)) (.next ([3765000000000], [1245000000000])
      (some (9, 2, 9)) (some (9, 2, 9)) (.next ([4860000000000], [2610000000000]) (some (9, 2, 9))
      (some (9, 2, 9)) (.next ([3390000000000], [1995000000000]) (some (7, 2, 9)) (some (7, 2, 9))
      (.next ([5745000000000], [3630000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next
      ([3255000000000], [2130000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next ([5745000000000],
      [3765000000000]) (some (7, 2, 9)) (some (7, 2, 9)) fan18Owner0Part1)))))))))))) (den :=
      9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_1 : ExcludedOn (model18.B 1 ++ [step18.q]) 9000000000000 (model18.caps 1)
    (model18.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4140000000000], [600000000000]) none none (.next
      ([1530000000000, 9000000000000], [1530000000000, 9000000000000]) none none (.next
      ([1530000000000, 9000000000000], [3210000000000, -9000000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([1530000000000, 9000000000000], [4140000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([0, 0], [2610000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-600000000000], [4740000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1530000000000,
      -9000000000000], [3060000000000, 18000000000000]) (some (3, 1, 2)) none (.next
      ([-3210000000000, 9000000000000], [4740000000000, 0]) none none (.next ([-4140000000000],
      [5670000000000, 9000000000000]) none none (.terminal none none none))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_3 : ExcludedOn (model18.B 3 ++ [step18.q]) 9000000000000 (model18.caps 3)
    (model18.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_4 : ExcludedOn (model18.B 4 ++ [step18.q]) 9000000000000 (model18.caps 4)
    (model18.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4140000000000], [2565000000000]) (some (2, 0,
      1)) (some (3, 0, 2)) (.next ([4140000000000], [4860000000000]) (some (3, 0, 2)) (some (3, 0,
      2)) (.next ([2610000000000, -9000000000000], [4860000000000]) (some (3, 0, 2)) (some (3, 0,
      2)) (.next ([765000000000, -9000000000000], [1530000000000, 9000000000000]) (some (3, 0, 2))
      (some (4, 0, 2)) (.next ([1530000000000, 9000000000000], [5175000000000, -9000000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([1530000000000, 9000000000000], [7470000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([0, 0], [7470000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-2565000000000], [6705000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-4860000000000], [9000000000000]) (some (4, 0, 2))
      (some (4, 0, 2)) (.next ([-4860000000000, 0], [7470000000000, -9000000000000]) (some (4, 0,
      2)) (some (4, 0, 2)) (.next ([-1530000000000, -9000000000000], [2295000000000]) (some (4, 0,
      2)) (some (4, 0, 2)) (.next ([-5175000000000, 9000000000000], [6705000000000, 0]) (some (4, 0,
      2)) (some (4, 0, 2)) (.next ([-7470000000000, 9000000000000], [9000000000000, 0]) (some (4, 0,
      2)) (some (4, 1, 2)) (.terminal (some (4, 1, 2)) (some (0, 1, 2)) (some (4, 1,
      2))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded18_8 : ExcludedOn (model18.B 8 ++ [step18.q]) 9000000000000 (model18.caps 8)
    (model18.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded18_3
    · exact excluded18_4
    · exact excluded18_5
    · exact excluded18_6
    · exact excluded18_7
    · exact excluded18_8
    · exact excluded18_9
theorem next18 : model18.insert step18 = model19 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded19_1 : ExcludedOn (model19.B 1 ++ [step19.q]) 9000000000000 (model19.caps 1)
    (model19.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2595000000000, -9000000000000], [0,
      9000000000000]) none none (.next ([3060000000000, 9000000000000], [1065000000000,
      -9000000000000]) none none (.next ([4125000000000], [3210000000000]) none none (.next
      ([1530000000000, 9000000000000], [1530000000000, 9000000000000]) none none (.next
      ([1530000000000, 9000000000000], [3210000000000, -9000000000000]) none none (.next ([0],
      [6270000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, -9000000000000],
      [2595000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1065000000000, 9000000000000],
      [4125000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3210000000000], [7335000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1530000000000, -9000000000000], [3060000000000,
      18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3210000000000, 9000000000000],
      [4740000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2)) none
      none))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded19_2 : ExcludedOn (model19.B 2 ++ [step19.q]) 9000000000000 (model19.caps 2)
    (model19.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2595000000000], [15000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([7500000000000, 0], [1020000000000, 9000000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([7470000000000, -9000000000000], [1530000000000, 9000000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([4860000000000, 0], [1530000000000, 9000000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([2595000000000], [4875000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([510000000000], [2130000000000]) (some (0, 4, 1)) (some (0, 4, 1))
      (.next ([1065000000000, -9000000000000], [6405000000000, 9000000000000]) (some (0, 4, 1))
      (some (0, 4, 2)) (.next ([510000000000], [6990000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([30000000000], [2085000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0],
      [1530000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-15000000000],
      [2610000000000]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([-1020000000000, -9000000000000],
      [8520000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1530000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1530000000000, -9000000000000], [6390000000000, 9000000000000]) (some (0, 1, 3)) (some (0,
      1, 3)) (.next ([-4875000000000], [7470000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-2130000000000], [2640000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-6405000000000,
      -9000000000000], [7470000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-6990000000000],
      [7500000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.next ([-2085000000000], [2115000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1, 3)) (some (4, 1, 0)) (some (4, 1,
      3))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded19_3 : ExcludedOn (model19.B 3 ++ [step19.q]) 9000000000000 (model19.caps 3)
    (model19.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_4 : ExcludedOn (model19.B 4 ++ [step19.q]) 9000000000000 (model19.caps 4)
    (model19.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_8 : ExcludedOn (model19.B 8 ++ [step19.q]) 9000000000000 (model19.caps 8)
    (model19.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded19_1
    · exact excluded19_2
    · exact excluded19_3
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
  apply ExclusionHint.sound (.witnessedFan (.next ([2880000000000], [90000000000]) (some (9, 1, 9))
      (some (9, 2, 9)) (.next ([1260000000000], [135000000000]) (some (9, 2, 9)) (some (9, 2, 9))
      (.next ([5760000000000], [1020000000000]) (some (9, 2, 9)) (some (9, 2, 9)) (.next
      ([2040000000000], [375000000000]) (some (9, 2, 9)) (some (9, 2, 9)) (.next ([5760000000000],
      [1155000000000]) (some (9, 2, 9)) (some (9, 2, 9)) (.next ([1905000000000], [510000000000])
      (some (9, 2, 9)) (some (9, 2, 9)) (.next ([5871000000000], [1599000000000]) (some (9, 2, 9))
      (some (9, 2, 9)) (.next ([3765000000000], [1110000000000]) (some (7, 2, 9)) (some (7, 2, 9))
      (.next ([3765000000000], [1245000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next
      ([5385000000000], [1905000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next ([6756000000000],
      [2619000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next ([5250000000000], [2040000000000])
      (some (7, 2, 9)) (some (7, 2, 9)) (.next ([6756000000000], [2754000000000]) (some (7, 2, 9))
      (some (7, 2, 9)) (.next ([2991000000000], [1509000000000]) (some (7, 2, 9)) (some (7, 2, 9))
      (.next ([4500000000000], [2415000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next
      ([6381000000000], [3504000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next ([4365000000000],
      [2415000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next ([6246000000000], [3639000000000])
      (some (7, 2, 9)) (some (7, 2, 9)) (.next ([3390000000000], [1995000000000]) (some (7, 2, 9))
      (some (7, 2, 9)) fan20Owner0Part1)))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3129000000000], [1611000000000]) none none
      (.next ([1530000000000, 9000000000000], [1530000000000, 9000000000000]) none none (.next
      ([1530000000000, 9000000000000], [3129000000000]) none none (.next ([0, 0], [1599000000000,
      -9000000000000]) none none (.next ([-1611000000000], [4740000000000]) (some (3, 1, 2)) none
      (.next ([-1530000000000, -9000000000000], [3060000000000, 18000000000000]) none none (.next
      ([-3129000000000], [4659000000000, 9000000000000]) none none (.terminal none none
      none))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded20_3 : ExcludedOn (model20.B 3 ++ [step20.q]) 9000000000000 (model20.caps 3)
    (model20.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_4 : ExcludedOn (model20.B 4 ++ [step20.q]) 9000000000000 (model20.caps 4)
    (model20.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([3129000000000], [3576000000000]) (some (2, 0,
      1)) (some (3, 0, 2)) (.next ([3129000000000], [5871000000000]) (some (3, 0, 2)) (some (3, 0,
      2)) (.next ([765000000000, -9000000000000], [1530000000000, 9000000000000]) (some (3, 0, 2))
      (some (3, 0, 2)) (.next ([1530000000000, 9000000000000], [5175000000000, -9000000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1599000000000, -9000000000000], [5871000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1530000000000, 9000000000000], [7470000000000,
      -9000000000000]) (some (3, 0, 2)) (some (4, 0, 2)) (.next ([0, 0], [7470000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-3576000000000], [6705000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-5871000000000], [9000000000000]) (some (4, 0, 2))
      (some (4, 0, 2)) (.next ([-1530000000000, -9000000000000], [2295000000000]) (some (4, 0, 2))
      (some (4, 0, 2)) (.next ([-5175000000000, 9000000000000], [6705000000000, 0]) (some (4, 0, 2))
      (some (4, 0, 2)) (.next ([-5871000000000, 0], [7470000000000, -9000000000000]) (some (4, 0,
      2)) (some (4, 1, 2)) (.next ([-7470000000000, 9000000000000], [9000000000000, 0]) (some (4, 1,
      2)) (some (4, 1, 2)) (.terminal (some (4, 1, 2)) (some (0, 1, 2)) (some (4, 1,
      2))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded20_8 : ExcludedOn (model20.B 8 ++ [step20.q]) 9000000000000 (model20.caps 8)
    (model20.ord 8) 0 1 100 := by
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
    · exact (hj rfl).elim
    · exact excluded20_3
    · exact excluded20_4
    · exact excluded20_5
    · exact excluded20_6
    · exact excluded20_7
    · exact excluded20_8
    · exact excluded20_9
theorem next20 : model20.insert step20 = model21 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded21_1 : ExcludedOn (model21.B 1 ++ [step21.q]) 9000000000000 (model21.caps 1)
    (model21.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2040000000000, 9000000000000], [960000000000,
      -9000000000000]) none none (.next ([1470000000000, -9000000000000], [1020000000000,
      9000000000000]) none none (.next ([1530000000000, 9000000000000], [1530000000000,
      9000000000000]) none none (.next ([3000000000000], [4230000000000]) none none (.next
      ([1530000000000, 9000000000000], [3210000000000, -9000000000000]) none none (.next ([0],
      [6270000000000, 9000000000000]) none none (.next ([-960000000000, 9000000000000],
      [3000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1020000000000, -9000000000000],
      [2490000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1530000000000,
      -9000000000000], [3060000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-4230000000000], [7230000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3210000000000,
      9000000000000], [4740000000000, 0]) (some (3, 1, 2)) none (.terminal none none
      none))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded21_2 : ExcludedOn (model21.B 2 ++ [step21.q]) 9000000000000 (model21.caps 2)
    (model21.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2490000000000], [129000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([7500000000000, 0], [1020000000000, 9000000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([7470000000000, -9000000000000], [1530000000000, 9000000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([5871000000000, 0], [1530000000000, 9000000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([1470000000000, -9000000000000], [1020000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([990000000000], [990000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([510000000000], [1119000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([2490000000000], [6000000000000]) (some (0, 4, 1)) (some (0, 4, 2))
      (.next ([960000000000, -9000000000000], [7530000000000, 9000000000000]) (some (0, 4, 2)) (some
      (0, 4, 2)) (.next ([510000000000], [6990000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([0, 0], [1530000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-129000000000], [2619000000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-1020000000000,
      -9000000000000], [8520000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-1530000000000, -9000000000000], [9000000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-1530000000000, -9000000000000], [7401000000000, 9000000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-1020000000000, -9000000000000], [2490000000000, 0]) (some (0, 4,
      3)) (some (0, 4, 3)) (.next ([-990000000000], [1980000000000]) (some (0, 4, 3)) (some (0, 4,
      3)) (.next ([-1119000000000], [1629000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-6000000000000], [8490000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-7530000000000,
      -9000000000000], [8490000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-6990000000000],
      [7500000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1, 3)) (some (4, 1,
      0)) (some (4, 1, 3))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded21_3 : ExcludedOn (model21.B 3 ++ [step21.q]) 9000000000000 (model21.caps 3)
    (model21.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_4 : ExcludedOn (model21.B 4 ++ [step21.q]) 9000000000000 (model21.caps 4)
    (model21.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_5 : ExcludedOn (model21.B 5 ++ [step21.q]) 9000000000000 (model21.caps 5)
    (model21.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_6 : ExcludedOn (model21.B 6 ++ [step21.q]) 9000000000000 (model21.caps 6)
    (model21.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8040000000000, 9000000000000], [1470000000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([6510000000000], [3000000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([3270000000000], [3000000000000]) (some (3, 0, 2))
      (some (3, 0, 2)) (.next ([1530000000000, 9000000000000], [3240000000000]) (some (3, 0, 2))
      (some (3, 0, 3)) (.next ([0, 0], [1530000000000, 9000000000000]) (some (3, 0, 3)) (some (3, 0,
      3)) (.next ([-1470000000000, 9000000000000], [9510000000000]) (some (3, 0, 3)) (some (3, 1,
      3)) (.next ([-3000000000000], [9510000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-3000000000000], [6270000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3240000000000,
      0], [4770000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1,
      3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded21_7 : ExcludedOn (model21.B 7 ++ [step21.q]) 9000000000000 (model21.caps 7)
    (model21.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_8 : ExcludedOn (model21.B 8 ++ [step21.q]) 9000000000000 (model21.caps 8)
    (model21.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded21_1
    · exact excluded21_2
    · exact excluded21_3
    · exact excluded21_4
    · exact excluded21_5
    · exact excluded21_6
    · exact excluded21_7
    · exact excluded21_8
    · exact excluded21_9
theorem next21 : model21.insert step21 = model22 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded22_1 : ExcludedOn (model22.B 1 ++ [step22.q]) 9000000000000 (model22.caps 1)
    (model22.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1905000000000, 9000000000000], [975000000000,
      -9000000000000]) none none (.next ([1350000000000, -9000000000000], [1155000000000,
      9000000000000]) none none (.next ([1530000000000, 9000000000000], [1530000000000,
      9000000000000]) none none (.next ([2880000000000], [4365000000000]) none none (.next
      ([1530000000000, 9000000000000], [3210000000000, -9000000000000]) none none (.next ([0],
      [6270000000000, 9000000000000]) none none (.next ([-975000000000, 9000000000000],
      [2880000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1155000000000, -9000000000000],
      [2505000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1530000000000,
      -9000000000000], [3060000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-4365000000000], [7245000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3210000000000,
      9000000000000], [4740000000000, 0]) (some (3, 1, 2)) none (.terminal none none
      none))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded22_2 : ExcludedOn (model22.B 2 ++ [step22.q]) 9000000000000 (model22.caps 2)
    (model22.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2505000000000], [249000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([7500000000000, 0], [1020000000000, 9000000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([7470000000000, -9000000000000], [1530000000000, 9000000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([5871000000000, 0], [1530000000000, 9000000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([1350000000000, -9000000000000], [1155000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([870000000000], [1125000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([510000000000], [1119000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([2505000000000], [6120000000000]) (some (0, 4, 1)) (some (0, 4, 2))
      (.next ([975000000000, -9000000000000], [7650000000000, 9000000000000]) (some (0, 4, 2)) (some
      (0, 4, 2)) (.next ([510000000000], [6990000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([0, 0], [1530000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-249000000000], [2754000000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-1020000000000,
      -9000000000000], [8520000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-1530000000000, -9000000000000], [9000000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-1530000000000, -9000000000000], [7401000000000, 9000000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-1155000000000, -9000000000000], [2505000000000, 0]) (some (0, 4,
      3)) (some (0, 4, 3)) (.next ([-1125000000000], [1995000000000]) (some (0, 4, 3)) (some (0, 4,
      3)) (.next ([-1119000000000], [1629000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-6120000000000], [8625000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-7650000000000,
      -9000000000000], [8625000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-6990000000000],
      [7500000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1, 3)) (some (4, 1,
      0)) (some (4, 1, 3))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_3 : ExcludedOn (model22.B 3 ++ [step22.q]) 9000000000000 (model22.caps 3)
    (model22.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_4 : ExcludedOn (model22.B 4 ++ [step22.q]) 9000000000000 (model22.caps 4)
    (model22.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_5 : ExcludedOn (model22.B 5 ++ [step22.q]) 9000000000000 (model22.caps 5)
    (model22.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_6 : ExcludedOn (model22.B 6 ++ [step22.q]) 9000000000000 (model22.caps 6)
    (model22.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8025000000000, 9000000000000], [1350000000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([6495000000000], [2880000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([3255000000000], [2880000000000]) (some (3, 0, 2))
      (some (3, 0, 2)) (.next ([1530000000000, 9000000000000], [3240000000000]) (some (3, 0, 2))
      (some (3, 0, 3)) (.next ([0, 0], [1530000000000, 9000000000000]) (some (3, 0, 3)) (some (3, 0,
      3)) (.next ([-1350000000000, 9000000000000], [9375000000000]) (some (3, 0, 3)) (some (3, 1,
      3)) (.next ([-2880000000000], [9375000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-2880000000000], [6135000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3240000000000,
      0], [4770000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1,
      3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_7 : ExcludedOn (model22.B 7 ++ [step22.q]) 9000000000000 (model22.caps 7)
    (model22.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_8 : ExcludedOn (model22.B 8 ++ [step22.q]) 9000000000000 (model22.caps 8)
    (model22.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded22_1
    · exact excluded22_2
    · exact excluded22_3
    · exact excluded22_4
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6885000000000], [135000000000]) (some (8, 1,
      11)) (some (8, 2, 11)) (.next ([2880000000000], [90000000000]) (some (8, 2, 11)) (some (8, 2,
      11)) (.next ([7995000000000], [615000000000]) (some (8, 2, 11)) (some (9, 2, 11)) (.next
      ([1155000000000], [90000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([7995000000000],
      [750000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([1020000000000], [105000000000])
      (some (9, 2, 11)) (some (9, 2, 11)) (.next ([1260000000000], [135000000000]) (some (9, 2, 11))
      (some (9, 2, 11)) (.next ([6630000000000], [750000000000]) (some (9, 2, 11)) (some (9, 2, 11))
      (.next ([6510000000000], [885000000000]) (some (9, 2, 11)) (some (9, 2, 11))
      fan23Owner0Part3))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded23_1 : ExcludedOn (model23.B 1 ++ [step23.q]) 9000000000000 (model23.caps 1)
    (model23.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1530000000000, 9000000000000], [1530000000000,
      9000000000000]) none none (.next ([360000000000, -9000000000000], [405000000000,
      9000000000000]) none none (.next ([1890000000000], [3615000000000]) none none (.next
      ([1530000000000, 9000000000000], [3210000000000, -9000000000000]) none none (.next
      ([765000000000, 9000000000000], [1890000000000]) none none (.next ([0], [6270000000000,
      9000000000000]) none none (.next ([-1530000000000, -9000000000000], [3060000000000,
      18000000000000]) none none (.next ([-405000000000, -9000000000000], [765000000000, 0]) none
      none (.next ([-3615000000000], [5505000000000]) none none (.next ([-3210000000000,
      9000000000000], [4740000000000, 0]) none none (.next ([-1890000000000], [2655000000000,
      9000000000000]) none none (.terminal none none none))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded23_3 : ExcludedOn (model23.B 3 ++ [step23.q]) 9000000000000 (model23.caps 3)
    (model23.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_4 : ExcludedOn (model23.B 4 ++ [step23.q]) 9000000000000 (model23.caps 4)
    (model23.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([360000000000, -9000000000000], [405000000000,
      9000000000000]) (some (2, 4, 1)) (some (3, 4, 2)) (.next ([765000000000, -9000000000000],
      [1530000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1890000000000],
      [5580000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1530000000000, 9000000000000],
      [5175000000000, -9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1890000000000],
      [7875000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1530000000000, 9000000000000],
      [7470000000000, -9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([360000000000,
      -9000000000000], [7875000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0, 0],
      [7470000000000, -9000000000000]) (some (3, 4, 2)) (some (4, 4, 2)) (.next ([-405000000000,
      -9000000000000], [765000000000, 0]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([-1530000000000,
      -9000000000000], [2295000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-5580000000000],
      [7470000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-5175000000000, 9000000000000],
      [6705000000000, 0]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-7875000000000],
      [9765000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([-7470000000000, 9000000000000],
      [9000000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-7875000000000, 0],
      [8235000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.terminal (some (4, 1, 2))
      (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded23_8 : ExcludedOn (model23.B 8 ++ [step23.q]) 9000000000000 (model23.caps 8)
    (model23.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

end Aown170000180000
end ConwaySoifer.Simplified.Certificates
