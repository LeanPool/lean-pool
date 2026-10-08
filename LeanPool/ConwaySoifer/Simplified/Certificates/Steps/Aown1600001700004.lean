/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown160000170000
import Mathlib.Tactic.FinCases

/-!
# Aown 160000 170000 4

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
namespace Aown160000170000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner0Part0 : FanWitness := (.next ([-261600000000, 2490000000000], [1058400000000,
    2490000000000]) (some (0, 4, 8)) (some (0, 5, 8)) (.next ([-2121600000000, 2490000000000],
    [8168400000000, 2490000000000]) (some (0, 5, 8)) (some (0, 5, 8)) (.next ([-2520000000000],
    [8430000000000]) (some (0, 5, 8)) (some (0, 5, 8)) (.next ([-690000000000], [2295000000000])
    (some (0, 5, 8)) (some (0, 5, 8)) (.next ([-2918400000000, -2490000000000], [8566800000000,
    4980000000000]) (some (0, 5, 6)) (some (0, 5, 6)) (.next ([-1650000000000], [4755000000000])
    (some (0, 5, 6)) (some (0, 5, 6)) (.next ([-3180000000000], [8430000000000]) (some (0, 5, 6))
    (some (0, 5, 6)) (.next ([-960000000000], [2460000000000]) (some (0, 5, 6)) (some (0, 5, 6))
    (.next ([-3316800000000, -4980000000000], [8168400000000, 2490000000000]) (some (0, 5, 6)) (some
    (1, 5, 7)) (.next ([-3726600000000, 2490000000000], [7478400000000, 2490000000000]) (some (1, 5,
    7)) (some (1, 5, 7)) (.next ([-398400000000, -2490000000000], [796800000000, 4980000000000])
    (some (1, 5, 7)) (some (1, 5, 7)) (.next ([-1140000000000], [2160000000000]) (some (1, 5, 7))
    (some (1, 5, 7)) (.next ([-4125000000000], [7740000000000]) (some (1, 5, 7)) (some (1, 5, 7))
    (.next ([-4523400000000, -2490000000000], [7876800000000, 4980000000000]) (some (1, 5, 7)) (some
    (1, 5, 7)) (.next ([-4785000000000], [7740000000000]) (some (1, 5, 7)) (some (1, 5, 7)) (.next
    ([-4921800000000, -4980000000000], [7478400000000, 2490000000000]) (some (2, 5, 7)) (some (2, 5,
    7)) (.next ([-796800000000, -4980000000000], [1058400000000, 2490000000000]) (some (2, 5, 7))
    (some (2, 5, 7)) (.next ([-5226600000000, 2490000000000], [6518400000000, 2490000000000]) (some
    (2, 5, 7)) (some (2, 5, 7)) (.next ([-5625000000000], [6780000000000]) (some (2, 5, 7)) (some
    (2, 5, 7)) (.next ([-6023400000000, -2490000000000], [6916800000000, 4980000000000]) (some (2,
    5, 7)) (some (2, 5, 7)) (.next ([-3435000000000], [3765000000000]) (some (2, 5, 7)) (some (2, 5,
    7)) (.next ([-6285000000000], [6780000000000]) (some (2, 5, 7)) (some (2, 5, 7)) (.next
    ([-6421800000000, -4980000000000], [6518400000000, 2490000000000]) (some (2, 5, 7)) (some (2, 5,
    7)) (.next ([-7148400000000, -2490000000000], [7186800000000, 4980000000000]) (some (2, 5, 7))
    (some (2, 5, 7)) (.terminal (some (2, 5, 7)) (some (2, 5, 7)) (some (2, 5,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner0Part1 : FanWitness := (.next ([5250000000000], [3180000000000]) (some (7, 2, 5))
    (some (7, 2, 5)) (.next ([1500000000000], [960000000000]) (some (7, 2, 5)) (some (7, 2, 5))
    (.next ([4851600000000, -2490000000000], [3316800000000, 4980000000000]) (some (7, 2, 5)) (some
    (7, 3, 5)) (.next ([3751800000000, 4980000000000], [3726600000000, -2490000000000]) (some (7, 3,
    5)) (some (7, 3, 5)) (.next ([398400000000, 2490000000000], [398400000000, 2490000000000]) (some
    (7, 3, 5)) (some (7, 3, 5)) (.next ([1020000000000], [1140000000000]) (some (7, 3, 5)) (some (7,
    3, 5)) (.next ([3615000000000], [4125000000000]) (some (7, 3, 5)) (some (7, 3, 8)) (.next
    ([3353400000000, 2490000000000], [4523400000000, 2490000000000]) (some (7, 3, 8)) (some (7, 3,
    8)) (.next ([2955000000000], [4785000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next
    ([2556600000000, -2490000000000], [4921800000000, 4980000000000]) (some (7, 4, 8)) (some (7, 4,
    8)) (.next ([261600000000, -2490000000000], [796800000000, 4980000000000]) (some (7, 4, 8))
    (some (7, 4, 8)) (.next ([1291800000000, 4980000000000], [5226600000000, -2490000000000]) (some
    (7, 4, 8)) (some (7, 4, 8)) (.next ([1155000000000], [5625000000000]) (some (0, 4, 8)) (some (0,
    4, 8)) (.next ([893400000000, 2490000000000], [6023400000000, 2490000000000]) (some (0, 4, 8))
    (some (0, 4, 8)) (.next ([330000000000], [3435000000000]) (some (0, 4, 8)) (some (0, 4, 8))
    (.next ([495000000000], [6285000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next ([96600000000,
    -2490000000000], [6421800000000, 4980000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next
    ([38400000000, 2490000000000], [7148400000000, 2490000000000]) (some (0, 4, 8)) (some (0, 4, 8))
    (.next ([0, 0], [1195200000000, 7470000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next
    ([-360000000000], [7410000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next ([-758400000000,
    -2490000000000], [7546800000000, 4980000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next
    ([-630000000000], [5895000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next ([-1020000000000],
    [7410000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next ([-1156800000000, -4980000000000],
    [7148400000000, 2490000000000]) (some (0, 4, 8)) (some (0, 4, 8))
    fan32Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner0Part0 : FanWitness := (.next ([-1020000000000], [7410000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-1156800000000, -4980000000000], [7148400000000, 2490000000000]) (some
    (0, 8, 6)) (some (0, 8, 6)) (.next ([-261600000000, 2490000000000], [1058400000000,
    2490000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-960000000000], [2460000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-3726600000000, 2490000000000], [7478400000000,
    2490000000000]) (some (0, 8, 6)) (some (1, 8, 7)) (.next ([-398400000000, -2490000000000],
    [796800000000, 4980000000000]) (some (1, 8, 7)) (some (1, 8, 7)) (.next ([-4125000000000],
    [7740000000000]) (some (1, 8, 7)) (some (1, 8, 7)) (.next ([-3885000000000], [7215000000000])
    (some (1, 8, 7)) (some (1, 8, 7)) (.next ([-4148400000000, -2490000000000], [7636800000000,
    4980000000000]) (some (1, 8, 7)) (some (1, 8, 7)) (.next ([-4523400000000, -2490000000000],
    [7876800000000, 4980000000000]) (some (1, 8, 7)) (some (1, 8, 7)) (.next ([-4410000000000],
    [7500000000000]) (some (1, 8, 7)) (some (1, 8, 7)) (.next ([-4785000000000], [7740000000000])
    (some (1, 8, 7)) (some (1, 8, 7)) (.next ([-4546800000000, -4980000000000], [7238400000000,
    2490000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.next ([-4410000000000], [6840000000000])
    (some (2, 8, 7)) (some (2, 8, 7)) (.next ([-4921800000000, -4980000000000], [7478400000000,
    2490000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.next ([-6345000000000], [8715000000000])
    (some (2, 8, 7)) (some (2, 8, 7)) (.next ([-796800000000, -4980000000000], [1058400000000,
    2490000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.next ([-5226600000000, 2490000000000],
    [6518400000000, 2490000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.next ([-5625000000000],
    [6780000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.next ([-6023400000000, -2490000000000],
    [6916800000000, 4980000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.next ([-3435000000000],
    [3765000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.next ([-6285000000000], [6780000000000])
    (some (2, 8, 7)) (some (2, 8, 7)) (.next ([-6421800000000, -4980000000000], [6518400000000,
    2490000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.next ([-7148400000000, -2490000000000],
    [7186800000000, 4980000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.terminal (some (2, 8, 7))
    (some (2, 8, 7)) (some (2, 8, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner0Part1 : FanWitness := (.next ([398400000000, 2490000000000], [398400000000,
    2490000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([3615000000000], [4125000000000])
    (some (7, 3, 5)) (some (7, 3, 5)) (.next ([3330000000000], [3885000000000]) (some (7, 3, 5))
    (some (7, 3, 5)) (.next ([3488400000000, 2490000000000], [4148400000000, 2490000000000]) (some
    (7, 3, 5)) (some (7, 3, 5)) (.next ([3353400000000, 2490000000000], [4523400000000,
    2490000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([3090000000000], [4410000000000])
    (some (7, 3, 5)) (some (7, 3, 5)) (.next ([2955000000000], [4785000000000]) (some (7, 3, 5))
    (some (7, 3, 5)) (.next ([2691600000000, -2490000000000], [4546800000000, 4980000000000]) (some
    (7, 4, 5)) (some (7, 4, 5)) (.next ([2430000000000], [4410000000000]) (some (7, 4, 5)) (some (7,
    4, 5)) (.next ([2556600000000, -2490000000000], [4921800000000, 4980000000000]) (some (7, 4, 5))
    (some (7, 8, 5)) (.next ([2370000000000], [6345000000000]) (some (7, 8, 5)) (some (7, 8, 5))
    (.next ([261600000000, -2490000000000], [796800000000, 4980000000000]) (some (7, 8, 5)) (some
    (7, 8, 5)) (.next ([1291800000000, 4980000000000], [5226600000000, -2490000000000]) (some (7, 8,
    5)) (some (7, 8, 5)) (.next ([1155000000000], [5625000000000]) (some (0, 8, 5)) (some (0, 8, 5))
    (.next ([893400000000, 2490000000000], [6023400000000, 2490000000000]) (some (0, 8, 5)) (some
    (0, 8, 5)) (.next ([330000000000], [3435000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next
    ([495000000000], [6285000000000]) (some (0, 8, 5)) (some (0, 8, 6)) (.next ([96600000000,
    -2490000000000], [6421800000000, 4980000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([38400000000, 2490000000000], [7148400000000, 2490000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([0, 0], [1195200000000, 7470000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([-360000000000], [7410000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-758400000000,
    -2490000000000], [7546800000000, 4980000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([-630000000000], [5895000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-450000000000],
    [3450000000000]) (some (0, 8, 6)) (some (0, 8, 6)) fan33Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner0Part0 : FanWitness := (.next ([-1125000000000], [8700000000000]) (some (0, 4, 8))
    (some (0, 4, 8)) (.next ([-1020000000000], [7410000000000]) (some (0, 4, 8)) (some (0, 4, 8))
    (.next ([-1156800000000, -4980000000000], [7148400000000, 2490000000000]) (some (0, 4, 8)) (some
    (0, 4, 8)) (.next ([-1523400000000, -2490000000000], [8836800000000, 4980000000000]) (some (0,
    4, 8)) (some (0, 5, 8)) (.next ([-1785000000000], [8700000000000]) (some (0, 5, 8)) (some (0, 5,
    8)) (.next ([-1921800000000, -4980000000000], [8438400000000, 2490000000000]) (some (0, 5, 8))
    (some (0, 5, 8)) (.next ([-960000000000], [3960000000000]) (some (0, 5, 8)) (some (0, 5, 8))
    (.next ([-1920000000000], [6420000000000]) (some (0, 5, 6)) (some (0, 5, 6)) (.next
    ([-960000000000], [2460000000000]) (some (0, 5, 6)) (some (0, 5, 6)) (.next ([-3726600000000,
    2490000000000], [7478400000000, 2490000000000]) (some (0, 5, 6)) (some (1, 5, 7)) (.next
    ([-398400000000, -2490000000000], [796800000000, 4980000000000]) (some (1, 5, 7)) (some (1, 5,
    7)) (.next ([-4125000000000], [7740000000000]) (some (1, 5, 7)) (some (1, 5, 7)) (.next
    ([-4523400000000, -2490000000000], [7876800000000, 4980000000000]) (some (1, 5, 7)) (some (1, 5,
    7)) (.next ([-765000000000], [1290000000000]) (some (1, 5, 7)) (some (1, 5, 7)) (.next
    ([-4785000000000], [7740000000000]) (some (1, 5, 7)) (some (2, 8, 7)) (.next ([-4921800000000,
    -4980000000000], [7478400000000, 2490000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.next
    ([-796800000000, -4980000000000], [1058400000000, 2490000000000]) (some (2, 8, 7)) (some (2, 8,
    7)) (.next ([-5226600000000, 2490000000000], [6518400000000, 2490000000000]) (some (2, 8, 7))
    (some (2, 8, 7)) (.next ([-5625000000000], [6780000000000]) (some (2, 8, 7)) (some (2, 8, 7))
    (.next ([-6023400000000, -2490000000000], [6916800000000, 4980000000000]) (some (2, 8, 7)) (some
    (2, 8, 7)) (.next ([-3435000000000], [3765000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.next
    ([-6285000000000], [6780000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.next ([-6421800000000,
    -4980000000000], [6518400000000, 2490000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.next
    ([-7148400000000, -2490000000000], [7186800000000, 4980000000000]) (some (2, 8, 7)) (some (2, 8,
    7)) (.terminal (some (2, 8, 7)) (some (2, 8, 7)) (some (2, 8, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner0Part1 : FanWitness := (.next ([6516600000000, -2490000000000], [1921800000000,
    4980000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([3000000000000], [960000000000]) (some
    (7, 2, 8)) (some (7, 2, 8)) (.next ([4500000000000], [1920000000000]) (some (7, 2, 8)) (some (7,
    2, 8)) (.next ([1500000000000], [960000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
    ([3751800000000, 4980000000000], [3726600000000, -2490000000000]) (some (7, 2, 8)) (some (7, 3,
    8)) (.next ([398400000000, 2490000000000], [398400000000, 2490000000000]) (some (7, 3, 8)) (some
    (7, 3, 8)) (.next ([3615000000000], [4125000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next
    ([3353400000000, 2490000000000], [4523400000000, 2490000000000]) (some (7, 3, 8)) (some (7, 3,
    8)) (.next ([525000000000], [765000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next
    ([2955000000000], [4785000000000]) (some (7, 3, 8)) (some (7, 4, 8)) (.next ([2556600000000,
    -2490000000000], [4921800000000, 4980000000000]) (some (7, 4, 8)) (some (7, 4, 8)) (.next
    ([261600000000, -2490000000000], [796800000000, 4980000000000]) (some (7, 4, 8)) (some (7, 4,
    8)) (.next ([1291800000000, 4980000000000], [5226600000000, -2490000000000]) (some (7, 4, 8))
    (some (7, 4, 8)) (.next ([1155000000000], [5625000000000]) (some (0, 4, 8)) (some (0, 4, 8))
    (.next ([893400000000, 2490000000000], [6023400000000, 2490000000000]) (some (0, 4, 8)) (some
    (0, 4, 8)) (.next ([330000000000], [3435000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next
    ([495000000000], [6285000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next ([96600000000,
    -2490000000000], [6421800000000, 4980000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next
    ([38400000000, 2490000000000], [7148400000000, 2490000000000]) (some (0, 4, 8)) (some (0, 4, 8))
    (.next ([0, 0], [1195200000000, 7470000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next
    ([-360000000000], [7410000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next ([-726600000000,
    2490000000000], [8438400000000, 2490000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next
    ([-758400000000, -2490000000000], [7546800000000, 4980000000000]) (some (0, 4, 8)) (some (0, 4,
    8)) (.next ([-630000000000], [5895000000000]) (some (0, 4, 8)) (some (0, 4, 8))
    fan34Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner0Part0 : FanWitness := (.next ([-1156800000000, -4980000000000], [7148400000000,
    2490000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-261600000000, 2490000000000],
    [1058400000000, 2490000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-960000000000],
    [2460000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-3726600000000, 2490000000000],
    [7478400000000, 2490000000000]) (some (0, 8, 6)) (some (1, 8, 7)) (.next ([-398400000000,
    -2490000000000], [796800000000, 4980000000000]) (some (1, 8, 7)) (some (1, 8, 7)) (.next
    ([-4125000000000], [7740000000000]) (some (1, 8, 7)) (some (1, 8, 7)) (.next ([-4523400000000,
    -2490000000000], [7876800000000, 4980000000000]) (some (1, 8, 7)) (some (1, 8, 7)) (.next
    ([-4785000000000], [7740000000000]) (some (1, 8, 7)) (some (1, 8, 7)) (.next ([-6083400000000,
    -2490000000000], [9796800000000, 4980000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.next
    ([-6345000000000], [9660000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.next ([-4921800000000,
    -4980000000000], [7478400000000, 2490000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.next
    ([-6481800000000, -4980000000000], [9398400000000, 2490000000000]) (some (2, 8, 7)) (some (2, 8,
    7)) (.next ([-6345000000000], [9000000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.next
    ([-6083400000000, -2490000000000], [8601600000000, -2490000000000]) (some (2, 8, 7)) (some (2,
    8, 7)) (.next ([-796800000000, -4980000000000], [1058400000000, 2490000000000]) (some (2, 8, 7))
    (some (2, 8, 7)) (.next ([-5226600000000, 2490000000000], [6518400000000, 2490000000000]) (some
    (2, 8, 7)) (some (2, 8, 7)) (.next ([-6045000000000], [7440000000000]) (some (2, 8, 7)) (some
    (2, 8, 7)) (.next ([-5625000000000], [6780000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.next
    ([-6023400000000, -2490000000000], [6916800000000, 4980000000000]) (some (2, 8, 7)) (some (2, 8,
    7)) (.next ([-3435000000000], [3765000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.next
    ([-6285000000000], [6780000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.next ([-8505000000000],
    [8940000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.next ([-6421800000000, -4980000000000],
    [6518400000000, 2490000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.next ([-7148400000000,
    -2490000000000], [7186800000000, 4980000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.terminal
    (some (2, 8, 7)) (some (2, 8, 7)) (some (2, 8, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner0Part1 : FanWitness := (.next ([3615000000000], [4125000000000]) (some (7, 3, 8))
    (some (7, 3, 8)) (.next ([3353400000000, 2490000000000], [4523400000000, 2490000000000]) (some
    (7, 3, 8)) (some (7, 3, 8)) (.next ([2955000000000], [4785000000000]) (some (7, 3, 8)) (some (7,
    3, 8)) (.next ([3713400000000, 2490000000000], [6083400000000, 2490000000000]) (some (7, 4, 8))
    (some (7, 4, 8)) (.next ([3315000000000], [6345000000000]) (some (7, 4, 8)) (some (7, 4, 8))
    (.next ([2556600000000, -2490000000000], [4921800000000, 4980000000000]) (some (7, 4, 8)) (some
    (7, 4, 8)) (.next ([2916600000000, -2490000000000], [6481800000000, 4980000000000]) (some (7, 4,
    8)) (some (7, 4, 8)) (.next ([2655000000000], [6345000000000]) (some (7, 4, 8)) (some (7, 4, 8))
    (.next ([2518200000000, -4980000000000], [6083400000000, 2490000000000]) (some (7, 4, 8)) (some
    (7, 4, 8)) (.next ([261600000000, -2490000000000], [796800000000, 4980000000000]) (some (7, 4,
    8)) (some (7, 8, 5)) (.next ([1291800000000, 4980000000000], [5226600000000, -2490000000000])
    (some (7, 8, 5)) (some (7, 8, 5)) (.next ([1395000000000], [6045000000000]) (some (0, 8, 5))
    (some (0, 8, 5)) (.next ([1155000000000], [5625000000000]) (some (0, 8, 5)) (some (0, 8, 5))
    (.next ([893400000000, 2490000000000], [6023400000000, 2490000000000]) (some (0, 8, 5)) (some
    (0, 8, 5)) (.next ([330000000000], [3435000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next
    ([495000000000], [6285000000000]) (some (0, 8, 5)) (some (0, 8, 6)) (.next ([435000000000],
    [8505000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([96600000000, -2490000000000],
    [6421800000000, 4980000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([38400000000,
    2490000000000], [7148400000000, 2490000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([0,
    0], [1195200000000, 7470000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-360000000000],
    [7410000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-758400000000, -2490000000000],
    [7546800000000, 4980000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-630000000000],
    [5895000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-1020000000000], [7410000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) fan35Owner0Part0))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7050000000000], [360000000000]) (some (7, 2, 5))
      (some (7, 2, 5)) (.next ([6788400000000, 2490000000000], [758400000000, 2490000000000]) (some
      (7, 2, 5)) (some (7, 2, 5)) (.next ([5265000000000], [630000000000]) (some (7, 2, 5)) (some
      (7, 2, 5)) (.next ([6390000000000], [1020000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
      ([5991600000000, -2490000000000], [1156800000000, 4980000000000]) (some (7, 2, 5)) (some (7,
      2, 5)) (.next ([796800000000, 4980000000000], [261600000000, -2490000000000]) (some (7, 2, 5))
      (some (7, 2, 5)) (.next ([6046800000000, 4980000000000], [2121600000000, -2490000000000])
      (some (7, 2, 5)) (some (7, 2, 5)) (.next ([5910000000000], [2520000000000]) (some (7, 2, 5))
      (some (7, 2, 5)) (.next ([1605000000000], [690000000000]) (some (7, 2, 5)) (some (7, 2, 5))
      (.next ([5648400000000, 2490000000000], [2918400000000, 2490000000000]) (some (7, 2, 5)) (some
      (7, 2, 5)) (.next ([3105000000000], [1650000000000]) (some (7, 2, 5)) (some (7, 2, 5))
      fan32Owner0Part1)))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded32_1 : ExcludedOn (model32.B 1 ++ [step32.q]) 9000000000000 (model32.caps 1)
    (model32.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3750000000000], [2160000000000]) none none
      (.next ([1440000000000, 9000000000000], [1440000000000, 9000000000000]) none none (.next
      ([1080000000000, -9000000000000], [1230000000000, 0]) none none (.next ([1440000000000,
      9000000000000], [3240000000000, -9000000000000]) none none (.next ([210000000000,
      9000000000000], [3750000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [6120000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2160000000000],
      [5910000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1440000000000, -9000000000000],
      [2880000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1230000000000,
      0], [2310000000000, -9000000000000]) (some (3, 1, 2)) none (.next ([-3240000000000,
      9000000000000], [4680000000000, 0]) none none (.next ([-3750000000000], [3960000000000,
      9000000000000]) none none (.terminal none none none))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded32_3 : ExcludedOn (model32.B 3 ++ [step32.q]) 9000000000000 (model32.caps 3)
    (model32.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_4 : ExcludedOn (model32.B 4 ++ [step32.q]) 9000000000000 (model32.caps 4)
    (model32.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([3750000000000], [4320000000000]) (some (2, 4,
      1)) (some (3, 4, 2)) (.next ([3750000000000], [6480000000000]) (some (3, 4, 2)) (some (3, 0,
      2)) (.next ([720000000000, -9000000000000], [1440000000000, 9000000000000]) (some (3, 0, 2))
      (some (3, 0, 2)) (.next ([2310000000000, -9000000000000], [6480000000000]) (some (3, 0, 2))
      (some (3, 0, 2)) (.next ([1440000000000, 9000000000000], [5400000000000, -9000000000000])
      (some (3, 0, 2)) (some (4, 0, 2)) (.next ([1440000000000, 9000000000000], [7560000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([0, 0], [7560000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-4320000000000], [8070000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-6480000000000], [10230000000000]) (some (4, 0, 2))
      (some (4, 0, 2)) (.next ([-1440000000000, -9000000000000], [2160000000000]) (some (4, 0, 2))
      (some (4, 0, 2)) (.next ([-6480000000000, 0], [8790000000000, -9000000000000]) (some (4, 0,
      2)) (some (4, 0, 2)) (.next ([-5400000000000, 9000000000000], [6840000000000, 0]) (some (4, 0,
      2)) (some (4, 0, 2)) (.next ([-7560000000000, 9000000000000], [9000000000000, 0]) (some (4, 0,
      2)) (some (4, 1, 2)) (.terminal (some (4, 1, 2)) (some (4, 1, 2)) (some (4, 1,
      2))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded32_8 : ExcludedOn (model32.B 8 ++ [step32.q]) 9000000000000 (model32.caps 8)
    (model32.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
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

theorem excluded33_0 : ExcludedOn (model33.B 0 ++ [step33.q]) 9000000000000 (model33.caps 0)
    (model33.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7050000000000], [360000000000]) (some (7, 2, 8))
      (some (7, 2, 8)) (.next ([6788400000000, 2490000000000], [758400000000, 2490000000000]) (some
      (7, 2, 8)) (some (7, 2, 8)) (.next ([5265000000000], [630000000000]) (some (7, 2, 8)) (some
      (7, 2, 8)) (.next ([3000000000000], [450000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
      ([6390000000000], [1020000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([5991600000000,
      -2490000000000], [1156800000000, 4980000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
      ([796800000000, 4980000000000], [261600000000, -2490000000000]) (some (7, 2, 5)) (some (7, 2,
      5)) (.next ([1500000000000], [960000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
      ([3751800000000, 4980000000000], [3726600000000, -2490000000000]) (some (7, 2, 5)) (some (7,
      3, 5)) fan33Owner0Part1)))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_1 : ExcludedOn (model33.B 1 ++ [step33.q]) 9000000000000 (model33.caps 1)
    (model33.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_2 : ExcludedOn (model33.B 2 ++ [step33.q]) 9000000000000 (model33.caps 2)
    (model33.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_3 : ExcludedOn (model33.B 3 ++ [step33.q]) 9000000000000 (model33.caps 3)
    (model33.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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

theorem excluded33_7 : ExcludedOn (model33.B 7 ++ [step33.q]) 9000000000000 (model33.caps 7)
    (model33.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7050000000000], [360000000000]) (some (7, 2, 8))
      (some (7, 2, 8)) (.next ([7711800000000, 4980000000000], [726600000000, -2490000000000]) (some
      (7, 2, 8)) (some (7, 2, 8)) (.next ([6788400000000, 2490000000000], [758400000000,
      2490000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([5265000000000], [630000000000])
      (some (7, 2, 8)) (some (7, 2, 8)) (.next ([7575000000000], [1125000000000]) (some (7, 2, 8))
      (some (7, 2, 8)) (.next ([6390000000000], [1020000000000]) (some (7, 2, 8)) (some (7, 2, 8))
      (.next ([5991600000000, -2490000000000], [1156800000000, 4980000000000]) (some (7, 2, 8))
      (some (7, 2, 8)) (.next ([7313400000000, 2490000000000], [1523400000000, 2490000000000]) (some
      (7, 2, 8)) (some (7, 2, 8)) (.next ([6915000000000], [1785000000000]) (some (7, 2, 8)) (some
      (7, 2, 8)) fan34Owner0Part1)))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_1 : ExcludedOn (model34.B 1 ++ [step34.q]) 9000000000000 (model34.caps 1)
    (model34.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([645000000000, -9000000000000], [315000000000,
      9000000000000]) none none (.next ([1440000000000, 9000000000000], [1440000000000,
      9000000000000]) none none (.next ([2085000000000], [3555000000000]) none none (.next
      ([1440000000000, 9000000000000], [3240000000000, -9000000000000]) none none (.next
      ([480000000000, 9000000000000], [2085000000000]) none none (.next ([0], [6120000000000,
      9000000000000]) none none (.next ([-315000000000, -9000000000000], [960000000000, 0]) none
      none (.next ([-1440000000000, -9000000000000], [2880000000000, 18000000000000]) none none
      (.next ([-3555000000000], [5640000000000]) none none (.next ([-3240000000000, 9000000000000],
      [4680000000000, 0]) none none (.next ([-2085000000000], [2565000000000, 9000000000000]) none
      none (.terminal none none none))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_3 : ExcludedOn (model34.B 3 ++ [step34.q]) 9000000000000 (model34.caps 3)
    (model34.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_7 : ExcludedOn (model34.B 7 ++ [step34.q]) 9000000000000 (model34.caps 7)
    (model34.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7050000000000], [360000000000]) (some (7, 2, 8))
      (some (7, 2, 8)) (.next ([6788400000000, 2490000000000], [758400000000, 2490000000000]) (some
      (7, 2, 8)) (some (7, 2, 8)) (.next ([5265000000000], [630000000000]) (some (7, 2, 8)) (some
      (7, 2, 8)) (.next ([6390000000000], [1020000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
      ([5991600000000, -2490000000000], [1156800000000, 4980000000000]) (some (7, 2, 8)) (some (7,
      2, 8)) (.next ([796800000000, 4980000000000], [261600000000, -2490000000000]) (some (7, 2, 8))
      (some (7, 2, 8)) (.next ([1500000000000], [960000000000]) (some (7, 2, 8)) (some (7, 2, 8))
      (.next ([3751800000000, 4980000000000], [3726600000000, -2490000000000]) (some (7, 2, 8))
      (some (7, 3, 8)) (.next ([398400000000, 2490000000000], [398400000000, 2490000000000]) (some
      (7, 3, 8)) (some (7, 3, 8)) fan35Owner0Part1)))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_1 : ExcludedOn (model35.B 1 ++ [step35.q]) 9000000000000 (model35.caps 1)
    (model35.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3315000000000, 0], [1440000000000,
      9000000000000]) none none (.next ([1440000000000, 9000000000000], [1440000000000,
      9000000000000]) (some (2, 3, 2)) (some (2, 3, 2)) (.next ([1440000000000, 9000000000000],
      [3240000000000, -9000000000000]) (some (2, 3, 2)) (some (2, 3, 2)) (.next ([0],
      [6120000000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-1440000000000,
      -9000000000000], [4755000000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next
      ([-1440000000000, -9000000000000], [2880000000000, 18000000000000]) (some (0, 3, 2)) (some (3,
      3, 2)) (.next ([-3240000000000, 9000000000000], [4680000000000, 0]) (some (3, 3, 2)) (some (3,
      3, 2)) (.terminal (some (3, 3, 2)) none none))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_2 : ExcludedOn (model35.B 2 ++ [step35.q]) 9000000000000 (model35.caps 2)
    (model35.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_3 : ExcludedOn (model35.B 3 ++ [step35.q]) 9000000000000 (model35.caps 3)
    (model35.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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

theorem excluded35_7 : ExcludedOn (model35.B 7 ++ [step35.q]) 9000000000000 (model35.caps 7)
    (model35.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_1 : ExcludedOn (model36.B 1 ++ [step36.q]) 9000000000000 (model36.caps 1)
    (model36.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_2 : ExcludedOn (model36.B 2 ++ [step36.q]) 9000000000000 (model36.caps 2)
    (model36.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_3 : ExcludedOn (model36.B 3 ++ [step36.q]) 9000000000000 (model36.caps 3)
    (model36.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_4 : ExcludedOn (model36.B 4 ++ [step36.q]) 9000000000000 (model36.caps 4)
    (model36.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5250000000000], [480000000000]) (some (3, 0, 2))
      (some (3, 1, 2)) (.next ([4785000000000, 0], [480000000000, 9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([4095000000000], [690000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([3345000000000], [945000000000]) (some (3, 1, 2)) (some (5, 1, 2)) (.next
      ([3810000000000, -9000000000000], [1920000000000, 9000000000000]) (some (5, 1, 2)) (some (5,
      1, 2)) (.next ([1695000000000, -9000000000000], [1440000000000, 9000000000000]) (some (5, 1,
      2)) (some (5, 1, 2)) (.next ([1440000000000, 9000000000000], [1440000000000, 9000000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2655000000000], [5730000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([960000000000], [2385000000000, -9000000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([960000000000], [3825000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([960000000000, 9000000000000], [4290000000000, -9000000000000]) (some (5, 1, 2)) (some
      (5, 1, 2)) (.next ([0, 0], [1440000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([-480000000000], [5730000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([-480000000000, -9000000000000], [5265000000000, 9000000000000]) (some (5, 1, 2)) (some (5,
      1, 2)) (.next ([-690000000000], [4785000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([-945000000000], [4290000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([-1920000000000,
      -9000000000000], [5730000000000, 0]) (some (5, 1, 2)) (some (5, 1, 3)) (.next
      ([-1440000000000, -9000000000000], [3135000000000]) (some (5, 1, 3)) (some (5, 2, 3)) (.next
      ([-1440000000000, -9000000000000], [2880000000000, 18000000000000]) (some (5, 2, 3)) (some (5,
      2, 3)) (.next ([-5730000000000], [8385000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-2385000000000, 9000000000000], [3345000000000, -9000000000000]) (some (5, 2, 3)) (some (5,
      2, 3)) (.next ([-3825000000000], [4785000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-4290000000000, 9000000000000], [5250000000000]) (some (5, 2, 3)) (some (5, 2, 3))
      (.terminal (some (5, 2, 3)) (some (0, 2, 3)) (some (5, 2, 3))))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_6 : ExcludedOn (model36.B 6 ++ [step36.q]) 9000000000000 (model36.caps 6)
    (model36.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_7 : ExcludedOn (model36.B 7 ++ [step36.q]) 9000000000000 (model36.caps 7)
    (model36.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded36_4
    · exact excluded36_5
    · exact excluded36_6
    · exact excluded36_7
    · exact (hj rfl).elim
    · exact excluded36_9
theorem next36 : model36.insert step36 = model37 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded37_0 : ExcludedOn (model37.B 0 ++ [step37.q]) 9000000000000 (model37.caps 0)
    (model37.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_1 : ExcludedOn (model37.B 1 ++ [step37.q]) 9000000000000 (model37.caps 1)
    (model37.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_2 : ExcludedOn (model37.B 2 ++ [step37.q]) 9000000000000 (model37.caps 2)
    (model37.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_3 : ExcludedOn (model37.B 3 ++ [step37.q]) 9000000000000 (model37.caps 3)
    (model37.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5475000000000], [555000000000]) (some (2, 4, 1))
      (some (4, 4, 1)) (.next ([6030000000000], [720000000000]) (some (4, 4, 1)) (some (4, 4, 2))
      (.next ([6195000000000], [1440000000000, 9000000000000]) (some (4, 4, 2)) (some (4, 4, 2))
      (.next ([4590000000000, -9000000000000], [2160000000000, 9000000000000]) (some (4, 4, 2))
      (some (4, 4, 2)) (.next ([6030000000000], [3165000000000]) (some (4, 4, 2)) (some (4, 4, 2))
      (.next ([1440000000000, 9000000000000], [1005000000000, -9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([0], [1440000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1,
      2)) (.next ([-555000000000], [6030000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-720000000000], [6750000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-1440000000000,
      -9000000000000], [7635000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-2160000000000, -9000000000000], [6750000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-3165000000000], [9195000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-1005000000000,
      9000000000000], [2445000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.terminal (some (4, 1, 2))
      (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_4 : ExcludedOn (model37.B 4 ++ [step37.q]) 9000000000000 (model37.caps 4)
    (model37.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_5 : ExcludedOn (model37.B 5 ++ [step37.q]) 9000000000000 (model37.caps 5)
    (model37.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_6 : ExcludedOn (model37.B 6 ++ [step37.q]) 9000000000000 (model37.caps 6)
    (model37.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_7 : ExcludedOn (model37.B 7 ++ [step37.q]) 9000000000000 (model37.caps 7)
    (model37.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded37_3
    · exact excluded37_4
    · exact excluded37_5
    · exact excluded37_6
    · exact excluded37_7
    · exact (hj rfl).elim
    · exact excluded37_9
theorem next37 : model37.insert step37 = model38 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded38_0 : ExcludedOn (model38.B 0 ++ [step38.q]) 9000000000000 (model38.caps 0)
    (model38.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_1 : ExcludedOn (model38.B 1 ++ [step38.q]) 9000000000000 (model38.caps 1)
    (model38.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_2 : ExcludedOn (model38.B 2 ++ [step38.q]) 9000000000000 (model38.caps 2)
    (model38.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_3 : ExcludedOn (model38.B 3 ++ [step38.q]) 9000000000000 (model38.caps 3)
    (model38.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5475000000000], [555000000000]) (some (2, 4, 1))
      (some (3, 4, 1)) (.next ([6030000000000], [720000000000]) (some (3, 4, 1)) (some (3, 4, 2))
      (.next ([2625000000000], [615000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([4590000000000, -9000000000000], [2160000000000, 9000000000000]) (some (3, 4, 2)) (some (3,
      4, 2)) (.next ([1185000000000, -9000000000000], [615000000000]) (some (3, 4, 2)) (some (3, 4,
      2)) (.next ([5580000000000], [3240000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([2790000000000], [3345000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0],
      [1440000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-555000000000],
      [6030000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-720000000000], [6750000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-615000000000], [3240000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-2160000000000, -9000000000000], [6750000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-615000000000], [1800000000000, -9000000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-3240000000000], [8820000000000]) (some (0, 1, 2)) (some (4, 1, 2))
      (.next ([-3345000000000], [6135000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.terminal (some
      (4, 1, 2)) (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded38_5 : ExcludedOn (model38.B 5 ++ [step38.q]) 9000000000000 (model38.caps 5)
    (model38.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_6 : ExcludedOn (model38.B 6 ++ [step38.q]) 9000000000000 (model38.caps 6)
    (model38.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_7 : ExcludedOn (model38.B 7 ++ [step38.q]) 9000000000000 (model38.caps 7)
    (model38.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_8 : ExcludedOn (model38.B 8 ++ [step38.q]) 9000000000000 (model38.caps 8)
    (model38.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3750000000000], [2625000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([3240000000000], [6375000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([690000000000], [5865000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([180000000000], [3060000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [5865000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2625000000000], [6375000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6375000000000], [9615000000000]) (some (0, 1, 2))
      (some (0, 3, 2)) (.next ([-5865000000000], [6555000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-3060000000000], [3240000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 5 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_1 : ExcludedOn (model39.B 1 ++ [step39.q]) 9000000000000 (model39.caps 1)
    (model39.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_2 : ExcludedOn (model39.B 2 ++ [step39.q]) 9000000000000 (model39.caps 2)
    (model39.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_3 : ExcludedOn (model39.B 3 ++ [step39.q]) 9000000000000 (model39.caps 3)
    (model39.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_5 : ExcludedOn (model39.B 5 ++ [step39.q]) 9000000000000 (model39.caps 5)
    (model39.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7470000000000, 0], [1440000000000,
      9000000000000]) (some (5, 0, 3)) (some (5, 1, 3)) (.next ([6750000000000], [2250000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1782000000000, 9000000000000], [810000000000,
      -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1530000000000], [720000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([5220000000000], [2592000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([1440000000000, 9000000000000], [1440000000000, 9000000000000]) (some
      (5, 1, 3)) (some (5, 1, 3)) (.next ([720000000000, 9000000000000], [2250000000000, 0]) (some
      (5, 1, 3)) (some (5, 1, 3)) (.next ([342000000000], [1188000000000]) (some (5, 1, 3)) (some
      (5, 1, 3)) (.next ([342000000000], [2250000000000]) (some (5, 1, 3)) (some (5, 1, 4)) (.next
      ([90000000000, -9000000000000], [720000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([0,
      0], [1440000000000, 9000000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([-1440000000000,
      -9000000000000], [8910000000000, 9000000000000]) (some (5, 1, 4)) (some (5, 2, 4)) (.next
      ([-2250000000000], [9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-810000000000,
      9000000000000], [2592000000000, 0]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-720000000000],
      [2250000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-2592000000000], [7812000000000])
      (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-1440000000000, -9000000000000], [2880000000000,
      18000000000000]) (some (5, 2, 4)) (some (5, 2, 5)) (.next ([-2250000000000, 0],
      [2970000000000, 9000000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-1188000000000],
      [1530000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-2250000000000], [2592000000000])
      (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-720000000000, 0], [810000000000, -9000000000000])
      (some (5, 2, 5)) (some (5, 2, 5)) (.terminal (some (5, 2, 5)) (some (0, 3, 5)) (some (5, 3,
      5))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded39_6 : ExcludedOn (model39.B 6 ++ [step39.q]) 9000000000000 (model39.caps 6)
    (model39.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_7 : ExcludedOn (model39.B 7 ++ [step39.q]) 9000000000000 (model39.caps 7)
    (model39.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

end Aown160000170000
end ConwaySoifer.Simplified.Certificates
