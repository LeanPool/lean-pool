/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext160000170000
import Mathlib.Tactic.FinCases

/-!
# Sext 160000 170000 4

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
namespace Sext160000170000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner4Part0 : FanWitness := (.next ([4725000000000], [1575000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([2250000000000], [870000000000]) (some (5, 1, 2)) (some (5, 1, 2))
    (.next ([3375000000000], [1890000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([1125000000000], [1020000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3855000000000],
    [4695000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1440000000000, 9000000000000],
    [4305000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1440000000000,
    9000000000000], [5175000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([480000000000],
    [1935000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([480000000000],
    [3375000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([570000000000], [5175000000000])
    (some (4, 1, 2)) (some (4, 1, 2)) (.next ([315000000000, 9000000000000], [3285000000000,
    -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0], [5175000000000]) (some (4, 1,
    2)) (some (4, 1, 2)) (.next ([-1125000000000], [4725000000000]) (some (0, 1, 2)) (some (0, 1,
    2)) (.next ([-1575000000000], [6300000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
    ([-870000000000], [3120000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1890000000000],
    [5265000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1020000000000], [2145000000000])
    (some (0, 1, 2)) (some (0, 1, 5)) (.next ([-4695000000000], [8550000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-4305000000000, 9000000000000], [5745000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-5175000000000], [6615000000000, 9000000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-1935000000000, 9000000000000], [2415000000000, -9000000000000]) (some
    (0, 1, 5)) (some (0, 1, 5)) (.next ([-3375000000000], [3855000000000]) (some (0, 1, 5)) (some
    (0, 1, 5)) (.next ([-5175000000000], [5745000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-3285000000000, 9000000000000], [3600000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.terminal
    (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner4Part1 : FanWitness := (.next ([4725000000000], [1575000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([2250000000000], [870000000000]) (some (5, 1, 2)) (some (5, 1, 2))
    (.next ([3375000000000], [1890000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([1125000000000], [1020000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3855000000000],
    [4695000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1440000000000, 9000000000000],
    [4305000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1440000000000,
    9000000000000], [5175000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([480000000000],
    [1935000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([480000000000],
    [3375000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([315000000000, 9000000000000],
    [3285000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([570000000000],
    [5175000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0], [5175000000000]) (some (4, 1,
    2)) (some (4, 1, 2)) (.next ([-1125000000000], [4725000000000]) (some (0, 1, 2)) (some (0, 1,
    2)) (.next ([-1575000000000], [6300000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
    ([-870000000000], [3120000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1890000000000],
    [5265000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1020000000000], [2145000000000])
    (some (0, 1, 2)) (some (0, 1, 5)) (.next ([-4695000000000], [8550000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-4305000000000, 9000000000000], [5745000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-5175000000000], [6615000000000, 9000000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-1935000000000, 9000000000000], [2415000000000, -9000000000000]) (some
    (0, 1, 5)) (some (0, 1, 5)) (.next ([-3375000000000], [3855000000000]) (some (0, 1, 5)) (some
    (0, 1, 5)) (.next ([-3285000000000, 9000000000000], [3600000000000]) (some (0, 1, 5)) (some (0,
    1, 5)) (.next ([-5175000000000], [5745000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.terminal
    (some (0, 1, 5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner3Part0 : FanWitness := (.next ([-375000000000], [4575000000000]) (some (0, 2, 8))
    (some (0, 2, 8)) (.next ([-480000000000], [5625000000000]) (some (0, 2, 8)) (some (0, 2, 8))
    (.next ([-375000000000], [2160000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next
    ([-1050000000000], [5400000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-1080000000000],
    [5250000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-960000000000], [2310000000000])
    (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-2400000000000], [4440000000000]) (some (0, 2, 8))
    (some (0, 2, 8)) (.next ([-2835000000000], [5025000000000]) (some (0, 2, 8)) (some (0, 2, 8))
    (.next ([-2430000000000], [4290000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next
    ([-1290000000000], [2250000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-3210000000000,
    9000000000000], [5400000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-5580000000000],
    [9180000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-5625000000000], [8745000000000])
    (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-4620000000000], [6870000000000]) (some (0, 2, 8))
    (some (0, 2, 8)) (.next ([-4665000000000], [6435000000000]) (some (0, 2, 8)) (some (0, 2, 8))
    (.next ([-5205000000000], [7020000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next
    ([-435000000000], [585000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-5580000000000, 0],
    [7020000000000, 9000000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-5250000000000],
    [6585000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-150000000000], [180000000000])
    (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-5625000000000, 0], [6585000000000, 9000000000000])
    (some (0, 2, 8)) (some (0, 3, 8)) (.next ([-4650000000000], [5400000000000]) (some (0, 3, 8))
    (some (0, 3, 8)) (.next ([-4680000000000], [5250000000000]) (some (0, 3, 8)) (some (0, 3, 8))
    (.next ([-435000000000], [480000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.terminal (some (0,
    3, 8)) (some (0, 3, 6)) (some (0, 3, 8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner3Part1 : FanWitness := (.next ([4170000000000], [1080000000000]) (some (7, 0, 3))
    (some (7, 0, 3)) (.next ([1350000000000], [960000000000]) (some (7, 0, 3)) (some (7, 0, 8))
    (.next ([2040000000000], [2400000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next
    ([2190000000000], [2835000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([1860000000000],
    [2430000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([960000000000], [1290000000000])
    (some (7, 0, 8)) (some (7, 0, 8)) (.next ([2190000000000, 9000000000000], [3210000000000,
    -9000000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([3600000000000], [5580000000000])
    (some (7, 0, 8)) (some (7, 0, 8)) (.next ([3120000000000], [5625000000000]) (some (7, 0, 8))
    (some (7, 0, 8)) (.next ([2250000000000], [4620000000000]) (some (7, 0, 8)) (some (7, 0, 8))
    (.next ([1770000000000], [4665000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next
    ([1815000000000], [5205000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([150000000000],
    [435000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([1440000000000, 9000000000000],
    [5580000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([1335000000000], [5250000000000])
    (some (7, 0, 8)) (some (7, 0, 8)) (.next ([30000000000], [150000000000]) (some (7, 0, 8)) (some
    (7, 0, 8)) (.next ([960000000000, 9000000000000], [5625000000000]) (some (7, 0, 8)) (some (7, 0,
    8)) (.next ([750000000000], [4650000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next
    ([570000000000], [4680000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([45000000000],
    [435000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([0], [5580000000000]) (some (7, 0, 8))
    (some (7, 1, 8)) (.next ([-180000000000], [4830000000000]) (some (0, 1, 8)) (some (0, 1, 8))
    (.next ([-225000000000], [4395000000000]) (some (0, 1, 8)) (some (0, 1, 8)) (.next
    ([-330000000000], [5010000000000]) (some (0, 1, 8)) (some (0, 2, 8))
    fan35Owner3Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan39Owner0Part0 : FanWitness := (.next ([-1335000000000], [7230000000000]) (some (9, 4, 5))
    (some (9, 4, 5)) (.next ([-660000000000], [3225000000000]) (some (9, 4, 5)) (some (9, 4, 5))
    (.next ([-261600000000, 2490000000000], [1058400000000, 2490000000000]) (some (9, 4, 5)) (some
    (9, 4, 5)) (.next ([-375000000000], [1515000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next
    ([-660000000000], [2565000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-796800000000,
    -4980000000000], [2963400000000, 2490000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next
    ([-3045000000000], [9315000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-136800000000,
    -4980000000000], [398400000000, 2490000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next
    ([-316800000000, -4980000000000], [773400000000, 2490000000000]) (some (9, 4, 5)) (some (9, 4,
    6)) (.next ([-180000000000], [375000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([-398400000000, -2490000000000], [796800000000, 4980000000000]) (some (9, 4, 6)) (some (9, 4,
    6)) (.next ([-3255000000000], [5550000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([-1920000000000], [3015000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-3735000000000],
    [5835000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-1035000000000], [1515000000000])
    (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-4133400000000, -2490000000000], [5971800000000,
    4980000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-855000000000], [1140000000000])
    (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-4395000000000], [5835000000000]) (some (9, 4, 7))
    (some (9, 4, 7)) (.next ([-4531800000000, -4980000000000], [5573400000000, 2490000000000]) (some
    (9, 4, 7)) (some (9, 4, 7)) (.next ([-1710000000000], [2085000000000]) (some (9, 4, 7)) (some
    (9, 4, 7)) (.next ([-4395000000000], [5175000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next
    ([-4215000000000], [4800000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-6270000000000],
    [6645000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-1253400000000, -2490000000000],
    [1276800000000, 4980000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.terminal (some (9, 4, 7))
    (some (9, 4, 7)) (some (9, 4, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan39Owner0Part1 : FanWitness := (.next ([456600000000, -2490000000000], [316800000000,
    4980000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([195000000000], [180000000000]) (some
    (9, 3, 4)) (some (9, 3, 4)) (.next ([398400000000, 2490000000000], [398400000000,
    2490000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([2295000000000], [3255000000000])
    (some (9, 3, 4)) (some (9, 3, 4)) (.next ([1095000000000], [1920000000000]) (some (9, 3, 4))
    (some (9, 3, 4)) (.next ([2100000000000], [3735000000000]) (some (9, 3, 4)) (some (9, 4, 4))
    (.next ([480000000000], [1035000000000]) (some (9, 4, 4)) (some (9, 4, 4)) (.next
    ([1838400000000, 2490000000000], [4133400000000, 2490000000000]) (some (9, 4, 4)) (some (9, 4,
    4)) (.next ([285000000000], [855000000000]) (some (9, 4, 4)) (some (9, 4, 4)) (.next
    ([1440000000000], [4395000000000]) (some (9, 4, 4)) (some (9, 4, 4)) (.next ([1041600000000,
    -2490000000000], [4531800000000, 4980000000000]) (some (9, 4, 4)) (some (9, 4, 4)) (.next
    ([375000000000], [1710000000000]) (some (9, 4, 4)) (some (9, 4, 4)) (.next ([780000000000],
    [4395000000000]) (some (9, 4, 4)) (some (9, 4, 4)) (.next ([585000000000], [4215000000000])
    (some (9, 4, 4)) (some (9, 4, 4)) (.next ([375000000000], [6270000000000]) (some (9, 4, 4))
    (some (9, 4, 4)) (.next ([23400000000, 2490000000000], [1253400000000, 2490000000000]) (some (9,
    4, 4)) (some (9, 4, 5)) (.next ([0], [660000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next
    ([-81600000000, 2490000000000], [7148400000000, 2490000000000]) (some (9, 4, 5)) (some (9, 4,
    5)) (.next ([-480000000000], [7410000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next
    ([-375000000000], [3420000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-878400000000,
    -2490000000000], [7546800000000, 4980000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next
    ([-1140000000000], [7410000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-180000000000],
    [1035000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-1125000000000], [6300000000000])
    (some (9, 4, 5)) (some (9, 4, 5)) fan39Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan39Owner3Part0 : FanWitness := (.next ([0], [5580000000000]) (some (6, 7, 5)) (some (6, 7, 5))
    (.next ([-480000000000], [5625000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-1185000000000], [3270000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-2580000000000],
    [5955000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-3015000000000], [6435000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-4185000000000], [8040000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-4620000000000], [8625000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-4995000000000, 9000000000000], [9000000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-1290000000000], [2250000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-3000000000000], [4770000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-3435000000000],
    [5355000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-3810000000000, 9000000000000],
    [5730000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-4620000000000], [6870000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-6435000000000], [9000000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-4665000000000], [6435000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-5205000000000], [7020000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-435000000000], [585000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-5580000000000, 0],
    [7020000000000, 9000000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-5250000000000],
    [6585000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-5625000000000, 0], [6585000000000,
    9000000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-435000000000], [480000000000]) (some
    (0, 7, 5)) (some (0, 7, 5)) (.next ([-5250000000000], [5730000000000]) (some (0, 7, 5)) (some
    (0, 7, 5)) (.next ([-5100000000000], [5250000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-4665000000000], [4770000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.terminal (some (0, 7,
    5)) (some (0, 7, 5)) (some (0, 7, 5)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_1 : ExcludedOn (model32.B 1 ++ [step32.q]) 9000000000000 (model32.caps 1)
    (model32.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_2 : ExcludedOn (model32.B 2 ++ [step32.q]) 9000000000000 (model32.caps 2)
    (model32.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_4 : ExcludedOn (model32.B 4 ++ [step32.q]) 9000000000000 (model32.caps 4)
    (model32.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (359) (766) (76600) (.witnessedFan (.next ([3600000000000],
      [1125000000000]) (some (5, 0, 2)) (some (5, 1, 2)) fan32Owner4Part0)) (.witnessedFan (.next
      ([3600000000000], [1125000000000]) (some (5, 0, 2)) (some (5, 1, 2)) fan32Owner4Part1))) (den
      := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_8 : ExcludedOn (model32.B 8 ++ [step32.q]) 9000000000000 (model32.caps 8)
    (model32.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5625000000000], [3855000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([2760000000000], [2865000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([1035000000000], [5580000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([45000000000], [3855000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [5580000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.next ([-3855000000000], [9480000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-2865000000000], [5625000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-5580000000000], [6615000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-3855000000000], [3900000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded32_9 : ExcludedOn (model32.B 9 ++ [step32.q]) 9000000000000 (model32.caps 9)
    (model32.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded32_4
    · exact excluded32_5
    · exact excluded32_6
    · exact excluded32_7
    · exact excluded32_8
    · exact excluded32_9
theorem next32 : model32.insert step32 = model33 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded33_0 : ExcludedOn (model33.B 0 ++ [step33.q]) 9000000000000 (model33.caps 0)
    (model33.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_1 : ExcludedOn (model33.B 1 ++ [step33.q]) 9000000000000 (model33.caps 1)
    (model33.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_2 : ExcludedOn (model33.B 2 ++ [step33.q]) 9000000000000 (model33.caps 2)
    (model33.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7185000000000], [375000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([3405000000000], [465000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([2595000000000], [375000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([2160000000000, 9000000000000], [1965000000000, -9000000000000]) (some (0, 4, 2)) (some (4,
      4, 2)) (.next ([3030000000000], [3435000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next
      ([1440000000000, 9000000000000], [4590000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([720000000000], [3405000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1065000000000,
      9000000000000], [7560000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0],
      [4590000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-375000000000], [7560000000000])
      (some (4, 1, 2)) (some (4, 1, 3)) (.next ([-465000000000], [3870000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([-375000000000], [2970000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([-1965000000000, 9000000000000], [4125000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([-3435000000000], [6465000000000]) (some (4, 1, 3)) (some (4, 2, 3)) (.next
      ([-4590000000000, 0], [6030000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-3405000000000], [4125000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-7560000000000,
      0], [8625000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some (4, 2,
      3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_4 : ExcludedOn (model33.B 4 ++ [step33.q]) 9000000000000 (model33.caps 4)
    (model33.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_5 : ExcludedOn (model33.B 5 ++ [step33.q]) 9000000000000 (model33.caps 5)
    (model33.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded33_4
    · exact excluded33_5
    · exact excluded33_6
    · exact excluded33_7
    · exact excluded33_8
    · exact excluded33_9
theorem next33 : model33.insert step33 = model34 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded34_0 : ExcludedOn (model34.B 0 ++ [step34.q]) 9000000000000 (model34.caps 0)
    (model34.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_1 : ExcludedOn (model34.B 1 ++ [step34.q]) 9000000000000 (model34.caps 1)
    (model34.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3405000000000], [465000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([6750000000000], [960000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([2160000000000], [960000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([2160000000000, 9000000000000], [1965000000000, -9000000000000]) (some (0, 4, 2)) (some (4,
      4, 2)) (.next ([2445000000000], [3585000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next
      ([1440000000000, 9000000000000], [4590000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([720000000000], [3405000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([480000000000,
      9000000000000], [7710000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0],
      [4590000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-465000000000], [3870000000000])
      (some (4, 1, 2)) (some (4, 1, 3)) (.next ([-960000000000], [7710000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([-960000000000], [3120000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([-1965000000000, 9000000000000], [4125000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([-3585000000000], [6030000000000]) (some (4, 1, 3)) (some (4, 2, 3)) (.next
      ([-4590000000000, 0], [6030000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-3405000000000], [4125000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-7710000000000,
      0], [8190000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some (4, 2,
      3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_4 : ExcludedOn (model34.B 4 ++ [step34.q]) 9000000000000 (model34.caps 4)
    (model34.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded34_9 : ExcludedOn (model34.B 9 ++ [step34.q]) 9000000000000 (model34.caps 9)
    (model34.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 3 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_1 : ExcludedOn (model35.B 1 ++ [step35.q]) 9000000000000 (model35.caps 1)
    (model35.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_3 : ExcludedOn (model35.B 3 ++ [step35.q]) 9000000000000 (model35.caps 3)
    (model35.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4650000000000], [180000000000]) (some (6, 0, 3))
      (some (7, 0, 3)) (.next ([4170000000000], [225000000000]) (some (7, 0, 3)) (some (7, 0, 3))
      (.next ([4680000000000], [330000000000]) (some (7, 0, 3)) (some (7, 0, 3)) (.next
      ([4200000000000], [375000000000]) (some (7, 0, 3)) (some (7, 0, 3)) (.next ([5145000000000],
      [480000000000]) (some (7, 0, 3)) (some (7, 0, 3)) (.next ([1785000000000], [375000000000])
      (some (7, 0, 3)) (some (7, 0, 3)) (.next ([4350000000000], [1050000000000]) (some (7, 0, 3))
      (some (7, 0, 3)) fan35Owner3Part1))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_4 : ExcludedOn (model35.B 4 ++ [step35.q]) 9000000000000 (model35.caps 4)
    (model35.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded35_3
    · exact excluded35_4
    · exact excluded35_5
    · exact excluded35_6
    · exact excluded35_7
    · exact excluded35_8
    · exact excluded35_9
theorem next35 : model35.insert step35 = model36 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded36_0 : ExcludedOn (model36.B 0 ++ [step36.q]) 9000000000000 (model36.caps 0)
    (model36.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_1 : ExcludedOn (model36.B 1 ++ [step36.q]) 9000000000000 (model36.caps 1)
    (model36.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_2 : ExcludedOn (model36.B 2 ++ [step36.q]) 9000000000000 (model36.caps 2)
    (model36.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_3 : ExcludedOn (model36.B 3 ++ [step36.q]) 9000000000000 (model36.caps 3)
    (model36.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5040000000000], [960000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([1875000000000], [435000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([960000000000], [465000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([3750000000000], [6465000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2790000000000],
      [6000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1875000000000], [6030000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([435000000000], [1440000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([1440000000000, 9000000000000], [6465000000000, 0]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([915000000000], [5565000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([480000000000, 9000000000000], [6000000000000, 0]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([0, 0], [1440000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([-960000000000], [6000000000000]) (some (5, 1, 2)) (some (5, 2, 2)) (.next ([-435000000000],
      [2310000000000]) (some (5, 2, 2)) (some (5, 2, 2)) (.next ([-465000000000], [1425000000000])
      (some (5, 2, 2)) (some (5, 2, 2)) (.next ([-6465000000000], [10215000000000]) (some (5, 2, 2))
      (some (5, 2, 3)) (.next ([-6000000000000], [8790000000000]) (some (5, 2, 3)) (some (5, 2, 3))
      (.next ([-6030000000000], [7905000000000]) (some (5, 2, 3)) (some (5, 2, 5)) (.next
      ([-1440000000000], [1875000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-6465000000000,
      0], [7905000000000, 9000000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next
      ([-5565000000000], [6480000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-6000000000000,
      0], [6480000000000, 9000000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.terminal (some (5, 2,
      5)) (some (0, 2, 5)) (some (5, 2, 5))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_9 : ExcludedOn (model36.B 9 ++ [step36.q]) 9000000000000 (model36.caps 9)
    (model36.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 4 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_1 : ExcludedOn (model37.B 1 ++ [step37.q]) 9000000000000 (model37.caps 1)
    (model37.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_2 : ExcludedOn (model37.B 2 ++ [step37.q]) 9000000000000 (model37.caps 2)
    (model37.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3405000000000], [1275000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([4080000000000], [1650000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([3030000000000], [2325000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([5190000000000, 9000000000000], [4290000000000, -9000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([2160000000000, 9000000000000], [1965000000000, -9000000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([3750000000000], [5730000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([1440000000000, 9000000000000], [5400000000000, 0]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([720000000000], [3405000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0],
      [5400000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1275000000000], [4680000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-1650000000000], [5730000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-2325000000000], [5355000000000]) (some (0, 4, 3)) (some (4, 4, 3))
      (.next ([-4290000000000, 9000000000000], [9480000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([-1965000000000, 9000000000000], [4125000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([-5730000000000], [9480000000000]) (some (4, 1, 3)) (some (4, 2, 3)) (.next
      ([-5400000000000, 0], [6840000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-3405000000000], [4125000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some (4, 2,
      3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_4 : ExcludedOn (model37.B 4 ++ [step37.q]) 9000000000000 (model37.caps 4)
    (model37.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2775000000000], [495000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([3600000000000], [1125000000000]) (some (5, 1, 2)) (some (5, 1, 5))
      (.next ([5250000000000], [1830000000000, -9000000000000]) (some (5, 1, 5)) (some (5, 1, 5))
      (.next ([4725000000000], [1650000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([5250000000000], [3270000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1125000000000],
      [1020000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1650000000000], [2145000000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1440000000000, 9000000000000], [4305000000000,
      -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1440000000000, 9000000000000],
      [5250000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([315000000000, 9000000000000],
      [3285000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([495000000000],
      [5250000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0], [5250000000000]) (some (4, 1,
      5)) (some (4, 1, 5)) (.next ([-495000000000], [3270000000000]) (some (0, 1, 5)) (some (0, 1,
      5)) (.next ([-1125000000000], [4725000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-1830000000000, 9000000000000], [7080000000000, -9000000000000]) (some (0, 1, 5)) (some (0,
      1, 5)) (.next ([-1650000000000], [6375000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-3270000000000], [8520000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-1020000000000], [2145000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-2145000000000], [3795000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4305000000000,
      9000000000000], [5745000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5250000000000],
      [6690000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3285000000000,
      9000000000000], [3600000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5250000000000],
      [5745000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.terminal (some (0, 1, 5)) (some (0, 2,
      5)) (some (0, 2, 5))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_5 : ExcludedOn (model37.B 5 ++ [step37.q]) 9000000000000 (model37.caps 5)
    (model37.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_9 : ExcludedOn (model37.B 9 ++ [step37.q]) 9000000000000 (model37.caps 9)
    (model37.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 4 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_1 : ExcludedOn (model38.B 1 ++ [step38.q]) 9000000000000 (model38.caps 1)
    (model38.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_2 : ExcludedOn (model38.B 2 ++ [step38.q]) 9000000000000 (model38.caps 2)
    (model38.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_3 : ExcludedOn (model38.B 3 ++ [step38.q]) 9000000000000 (model38.caps 3)
    (model38.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_5 : ExcludedOn (model38.B 5 ++ [step38.q]) 9000000000000 (model38.caps 5)
    (model38.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5040000000000], [960000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([1590000000000], [435000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([960000000000], [465000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([3465000000000], [6465000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2505000000000],
      [6000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1875000000000], [6030000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([435000000000], [1440000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([1440000000000, 9000000000000], [6465000000000, 0]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([915000000000], [5565000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([480000000000, 9000000000000], [6000000000000, 0]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([0, 0], [1440000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([-960000000000], [6000000000000]) (some (5, 1, 2)) (some (5, 2, 2)) (.next ([-435000000000],
      [2025000000000]) (some (5, 2, 2)) (some (5, 2, 2)) (.next ([-465000000000], [1425000000000])
      (some (5, 2, 2)) (some (5, 2, 2)) (.next ([-6465000000000], [9930000000000]) (some (5, 2, 2))
      (some (5, 2, 3)) (.next ([-6000000000000], [8505000000000]) (some (5, 2, 3)) (some (5, 2, 3))
      (.next ([-6030000000000], [7905000000000]) (some (5, 2, 3)) (some (5, 2, 5)) (.next
      ([-1440000000000], [1875000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-6465000000000,
      0], [7905000000000, 9000000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next
      ([-5565000000000], [6480000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-6000000000000,
      0], [6480000000000, 9000000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.terminal (some (5, 2,
      5)) (some (0, 2, 5)) (some (5, 2, 5))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded38_6 : ExcludedOn (model38.B 6 ++ [step38.q]) 9000000000000 (model38.caps 6)
    (model38.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded38_1
    · exact excluded38_2
    · exact excluded38_3
    · exact (hj rfl).elim
    · exact excluded38_5
    · exact excluded38_6
    · exact excluded38_7
    · exact excluded38_8
    · exact excluded38_9
theorem next38 : model38.insert step38 = model39 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded39_0 : ExcludedOn (model39.B 0 ++ [step39.q]) 9000000000000 (model39.caps 0)
    (model39.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7066800000000, 4980000000000], [81600000000,
      -2490000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next ([6930000000000], [480000000000])
      (some (7, 9, 4)) (some (7, 9, 4)) (.next ([3045000000000], [375000000000]) (some (7, 9, 4))
      (some (7, 9, 4)) (.next ([6668400000000, 2490000000000], [878400000000, 2490000000000]) (some
      (7, 9, 4)) (some (7, 9, 4)) (.next ([6270000000000], [1140000000000]) (some (7, 9, 4)) (some
      (7, 9, 4)) (.next ([855000000000], [180000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next
      ([5175000000000], [1125000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next ([5895000000000],
      [1335000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([2565000000000], [660000000000])
      (some (7, 3, 4)) (some (7, 3, 4)) (.next ([796800000000, 4980000000000], [261600000000,
      -2490000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([1140000000000], [375000000000])
      (some (7, 3, 4)) (some (7, 3, 4)) (.next ([1905000000000], [660000000000]) (some (7, 3, 4))
      (some (7, 3, 4)) (.next ([2166600000000, -2490000000000], [796800000000, 4980000000000]) (some
      (7, 3, 4)) (some (7, 3, 4)) (.next ([6270000000000], [3045000000000]) (some (7, 3, 4)) (some
      (9, 3, 4)) (.next ([261600000000, -2490000000000], [136800000000, 4980000000000]) (some (9, 3,
      4)) (some (9, 3, 4)) fan39Owner0Part1)))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded39_1 : ExcludedOn (model39.B 1 ++ [step39.q]) 9000000000000 (model39.caps 1)
    (model39.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_2 : ExcludedOn (model39.B 2 ++ [step39.q]) 9000000000000 (model39.caps 2)
    (model39.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_3 : ExcludedOn (model39.B 3 ++ [step39.q]) 9000000000000 (model39.caps 3)
    (model39.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5145000000000], [480000000000]) (some (5, 0, 7))
      (some (6, 0, 7)) (.next ([2085000000000], [1185000000000]) (some (6, 0, 7)) (some (6, 0, 7))
      (.next ([3375000000000], [2580000000000]) (some (6, 0, 2)) (some (6, 0, 2)) (.next
      ([3420000000000], [3015000000000]) (some (6, 0, 2)) (some (6, 0, 2)) (.next ([3855000000000],
      [4185000000000]) (some (6, 0, 2)) (some (6, 7, 2)) (.next ([4005000000000], [4620000000000])
      (some (6, 7, 2)) (some (6, 7, 2)) (.next ([4005000000000, 9000000000000], [4995000000000,
      -9000000000000]) (some (6, 7, 2)) (some (6, 7, 2)) (.next ([960000000000], [1290000000000])
      (some (6, 7, 2)) (some (6, 7, 2)) (.next ([1770000000000], [3000000000000]) (some (6, 7, 2))
      (some (6, 7, 2)) (.next ([1920000000000], [3435000000000]) (some (6, 7, 2)) (some (6, 7, 3))
      (.next ([1920000000000, 9000000000000], [3810000000000, -9000000000000]) (some (6, 7, 3))
      (some (6, 7, 3)) (.next ([2250000000000], [4620000000000]) (some (6, 7, 3)) (some (6, 7, 3))
      (.next ([2565000000000], [6435000000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next
      ([1770000000000], [4665000000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next ([1815000000000],
      [5205000000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next ([150000000000], [435000000000])
      (some (6, 7, 3)) (some (6, 7, 3)) (.next ([1440000000000, 9000000000000], [5580000000000])
      (some (6, 7, 3)) (some (6, 7, 4)) (.next ([1335000000000], [5250000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([960000000000, 9000000000000], [5625000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([45000000000], [435000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([480000000000], [5250000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next
      ([150000000000], [5100000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next ([105000000000],
      [4665000000000]) (some (6, 7, 5)) (some (6, 7, 5)) fan39Owner3Part0))))))))))))))))))))))))
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded39_5 : ExcludedOn (model39.B 5 ++ [step39.q]) 9000000000000 (model39.caps 5)
    (model39.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_9 : ExcludedOn (model39.B 9 ++ [step39.q]) 9000000000000 (model39.caps 9)
    (model39.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked39 : StepValid model39 9000000000000 step39 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded39_0
    · exact excluded39_1
    · exact excluded39_2
    · exact excluded39_3
    · exact (hj rfl).elim
    · exact excluded39_5
    · exact excluded39_6
    · exact excluded39_7
    · exact excluded39_8
    · exact excluded39_9
theorem next39 : model39.insert step39 = model40 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext160000170000
end ConwaySoifer.Simplified.Certificates
