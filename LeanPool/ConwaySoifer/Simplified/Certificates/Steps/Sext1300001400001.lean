/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext130000140000
import Mathlib.Tactic.FinCases

/-!
# Sext 130000 140000 1

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
namespace Sext130000140000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan12Owner0Part0 : FanWitness := (.next ([-1140000000000], [6690000000000]) (some (8, 2, 5))
    (some (8, 2, 5)) (.next ([-1115400000000, -2580000000000], [5619600000000, -2580000000000])
    (some (8, 2, 5)) (some (8, 2, 5)) (.next ([-1450800000000, -5160000000000], [6290400000000,
    2580000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([-225000000000], [735000000000]) (some
    (8, 2, 5)) (some (8, 2, 5)) (.next ([-255000000000], [765000000000]) (some (8, 2, 5)) (some (8,
    3, 5)) (.next ([-695400000000, -2580000000000], [1405800000000, 5160000000000]) (some (8, 3, 5))
    (some (8, 3, 5)) (.next ([-335400000000, -2580000000000], [670800000000, 5160000000000]) (some
    (8, 3, 5)) (some (8, 3, 5)) (.next ([-4830000000000], [9540000000000]) (some (8, 3, 5)) (some
    (8, 3, 5)) (.next ([-195000000000], [375000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next
    ([-5565000000000], [10050000000000]) (some (8, 3, 5)) (some (8, 3, 7)) (.next ([-5595000000000],
    [10050000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-3990000000000], [5850000000000])
    (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-875400000000, -2580000000000], [1210800000000,
    5160000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-4365000000000], [6030000000000])
    (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-4700400000000, -2580000000000], [6160800000000,
    5160000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-4500000000000], [5625000000000])
    (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-4500000000000], [5595000000000]) (some (8, 3, 7))
    (some (8, 3, 7)) (.next ([-4875000000000], [5805000000000]) (some (8, 3, 7)) (some (8, 3, 7))
    (.next ([-4875000000000], [5775000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next
    ([-5035800000000, -5160000000000], [5825400000000, 2580000000000]) (some (8, 3, 7)) (some (8, 3,
    7)) (.next ([-5210400000000, -2580000000000], [5935800000000, 5160000000000]) (some (8, 3, 7))
    (some (8, 3, 7)) (.next ([-5210400000000, -2580000000000], [5905800000000, 5160000000000]) (some
    (8, 3, 7)) (some (8, 3, 7)) (.next ([-4700400000000, -2580000000000], [5154600000000,
    -2580000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-5545800000000, -5160000000000],
    [5600400000000, 2580000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.terminal (some (8, 3, 7))
    (some (8, 3, 7)) (some (8, 3, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan12Owner0Part1 : FanWitness := (.next ([510000000000], [255000000000]) (some (8, 8, 4)) (some
    (8, 8, 4)) (.next ([710400000000, 2580000000000], [695400000000, 2580000000000]) (some (8, 8,
    4)) (some (8, 8, 4)) (.next ([335400000000, 2580000000000], [335400000000, 2580000000000]) (some
    (8, 8, 4)) (some (8, 8, 4)) (.next ([4710000000000], [4830000000000]) (some (8, 8, 4)) (some (8,
    8, 4)) (.next ([180000000000], [195000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
    ([4485000000000], [5565000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([4455000000000],
    [5595000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([1860000000000], [3990000000000])
    (some (8, 2, 4)) (some (8, 2, 4)) (.next ([335400000000, 2580000000000], [875400000000,
    2580000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([1665000000000], [4365000000000])
    (some (8, 2, 4)) (some (8, 2, 4)) (.next ([1460400000000, 2580000000000], [4700400000000,
    2580000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([1125000000000], [4500000000000])
    (some (8, 2, 4)) (some (8, 2, 4)) (.next ([1095000000000], [4500000000000]) (some (8, 2, 4))
    (some (8, 2, 4)) (.next ([930000000000], [4875000000000]) (some (8, 2, 4)) (some (8, 2, 5))
    (.next ([900000000000], [4875000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next
    ([789600000000, -2580000000000], [5035800000000, 5160000000000]) (some (8, 2, 5)) (some (8, 2,
    5)) (.next ([725400000000, 2580000000000], [5210400000000, 2580000000000]) (some (8, 2, 5))
    (some (8, 2, 5)) (.next ([695400000000, 2580000000000], [5210400000000, 2580000000000]) (some
    (8, 2, 5)) (some (8, 2, 5)) (.next ([454200000000, -5160000000000], [4700400000000,
    2580000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([54600000000, -2580000000000],
    [5545800000000, 5160000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([24600000000,
    -2580000000000], [5545800000000, 5160000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next
    ([-280800000000, -5160000000000], [5210400000000, 2580000000000]) (some (8, 2, 5)) (some (8, 2,
    5)) (.next ([-310800000000, -5160000000000], [5210400000000, 2580000000000]) (some (8, 2, 5))
    (some (8, 2, 5)) (.next ([-444600000000, 2580000000000], [5284200000000, -5160000000000]) (some
    (8, 2, 5)) (some (8, 2, 5)) fan12Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan13Owner0Part0 : FanWitness := (.next ([-695400000000, -2580000000000], [1405800000000,
    5160000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-335400000000, -2580000000000],
    [670800000000, 5160000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-195000000000],
    [375000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-5475000000000], [9360000000000])
    (some (8, 3, 5)) (some (8, 3, 7)) (.next ([-4779600000000, 2580000000000], [7954200000000,
    -5160000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-5655000000000], [9165000000000])
    (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-5785800000000, -5160000000000], [8960400000000,
    2580000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-5450400000000, -2580000000000],
    [8289600000000, -2580000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-3990000000000],
    [5850000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-875400000000, -2580000000000],
    [1210800000000, 5160000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-4365000000000],
    [6030000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-4700400000000, -2580000000000],
    [6160800000000, 5160000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-4500000000000],
    [5625000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-4500000000000], [5595000000000])
    (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-4875000000000], [5805000000000]) (some (8, 3, 7))
    (some (8, 3, 7)) (.next ([-4875000000000], [5775000000000]) (some (8, 3, 7)) (some (8, 3, 7))
    (.next ([-5035800000000, -5160000000000], [5825400000000, 2580000000000]) (some (8, 3, 7)) (some
    (8, 3, 7)) (.next ([-5210400000000, -2580000000000], [5935800000000, 5160000000000]) (some (8,
    3, 7)) (some (8, 3, 7)) (.next ([-5210400000000, -2580000000000], [5905800000000,
    5160000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-4700400000000, -2580000000000],
    [5154600000000, -2580000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-7500000000000],
    [7875000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-8235000000000], [8385000000000])
    (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-8265000000000], [8385000000000]) (some (8, 3, 7))
    (some (8, 3, 7)) (.next ([-5545800000000, -5160000000000], [5600400000000, 2580000000000]) (some
    (8, 3, 7)) (some (8, 3, 7)) (.terminal (some (8, 3, 7)) (some (8, 3, 7)) (some (8, 3,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan13Owner0Part1 : FanWitness := (.next ([3174600000000, -2580000000000], [5785800000000,
    5160000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([2839200000000, -5160000000000],
    [5450400000000, 2580000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([1860000000000],
    [3990000000000]) (some (0, 8, 4)) (some (8, 8, 4)) (.next ([335400000000, 2580000000000],
    [875400000000, 2580000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next ([1665000000000],
    [4365000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next ([1460400000000, 2580000000000],
    [4700400000000, 2580000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next ([1125000000000],
    [4500000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next ([1095000000000], [4500000000000])
    (some (8, 8, 4)) (some (8, 8, 4)) (.next ([930000000000], [4875000000000]) (some (8, 8, 4))
    (some (8, 8, 5)) (.next ([900000000000], [4875000000000]) (some (8, 8, 5)) (some (8, 8, 5))
    (.next ([789600000000, -2580000000000], [5035800000000, 5160000000000]) (some (8, 8, 5)) (some
    (8, 8, 5)) (.next ([725400000000, 2580000000000], [5210400000000, 2580000000000]) (some (8, 8,
    5)) (some (8, 8, 5)) (.next ([695400000000, 2580000000000], [5210400000000, 2580000000000])
    (some (8, 8, 5)) (some (8, 8, 5)) (.next ([454200000000, -5160000000000], [4700400000000,
    2580000000000]) (some (8, 8, 5)) (some (8, 8, 5)) (.next ([375000000000], [7500000000000]) (some
    (8, 8, 5)) (some (8, 8, 5)) (.next ([150000000000], [8235000000000]) (some (8, 2, 5)) (some (8,
    2, 5)) (.next ([120000000000], [8265000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next
    ([54600000000, -2580000000000], [5545800000000, 5160000000000]) (some (8, 2, 5)) (some (8, 2,
    5)) (.next ([24600000000, -2580000000000], [5545800000000, 5160000000000]) (some (8, 2, 5))
    (some (8, 2, 5)) (.next ([-280800000000, -5160000000000], [5210400000000, 2580000000000]) (some
    (8, 2, 5)) (some (8, 2, 5)) (.next ([-310800000000, -5160000000000], [5210400000000,
    2580000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([-204600000000, 2580000000000],
    [875400000000, 2580000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([-225000000000],
    [735000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([-255000000000], [765000000000]) (some
    (8, 2, 5)) (some (8, 3, 5)) fan13Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner0Part0 : FanWitness := (.next ([-204600000000, 2580000000000], [875400000000,
    2580000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([-225000000000], [735000000000]) (some
    (8, 2, 5)) (some (8, 2, 5)) (.next ([-255000000000], [765000000000]) (some (8, 2, 5)) (some (8,
    3, 5)) (.next ([-695400000000, -2580000000000], [1405800000000, 5160000000000]) (some (8, 3, 5))
    (some (8, 3, 5)) (.next ([-335400000000, -2580000000000], [670800000000, 5160000000000]) (some
    (8, 3, 5)) (some (8, 3, 5)) (.next ([-195000000000], [375000000000]) (some (8, 3, 5)) (some (8,
    3, 5)) (.next ([-6000000000000], [9735000000000]) (some (8, 3, 5)) (some (8, 3, 7)) (.next
    ([-5304600000000, 2580000000000], [8329200000000, -5160000000000]) (some (8, 3, 7)) (some (8, 3,
    7)) (.next ([-6180000000000], [9540000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next
    ([-6310800000000, -5160000000000], [9335400000000, 2580000000000]) (some (8, 3, 7)) (some (8, 3,
    7)) (.next ([-3990000000000], [5850000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next
    ([-5975400000000, -2580000000000], [8664600000000, -2580000000000]) (some (8, 3, 7)) (some (8,
    3, 7)) (.next ([-875400000000, -2580000000000], [1210800000000, 5160000000000]) (some (8, 3, 7))
    (some (8, 3, 7)) (.next ([-4365000000000], [6030000000000]) (some (8, 3, 7)) (some (8, 3, 7))
    (.next ([-4700400000000, -2580000000000], [6160800000000, 5160000000000]) (some (8, 3, 7)) (some
    (8, 3, 7)) (.next ([-4500000000000], [5625000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next
    ([-4500000000000], [5595000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-4875000000000],
    [5805000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-4875000000000], [5775000000000])
    (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-5035800000000, -5160000000000], [5825400000000,
    2580000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-5210400000000, -2580000000000],
    [5935800000000, 5160000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-5210400000000,
    -2580000000000], [5905800000000, 5160000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next
    ([-4700400000000, -2580000000000], [5154600000000, -2580000000000]) (some (8, 3, 7)) (some (8,
    3, 7)) (.next ([-5545800000000, -5160000000000], [5600400000000, 2580000000000]) (some (8, 3,
    7)) (some (8, 3, 7)) (.terminal (some (8, 3, 7)) (some (8, 3, 7)) (some (8, 3,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner0Part1 : FanWitness := (.next ([3735000000000], [6000000000000]) (some (0, 8, 4))
    (some (0, 8, 4)) (.next ([3024600000000, -2580000000000], [5304600000000, -2580000000000]) (some
    (0, 8, 4)) (some (0, 8, 4)) (.next ([3360000000000], [6180000000000]) (some (0, 8, 4)) (some (0,
    8, 4)) (.next ([3024600000000, -2580000000000], [6310800000000, 5160000000000]) (some (0, 8, 4))
    (some (0, 8, 4)) (.next ([1860000000000], [3990000000000]) (some (0, 8, 4)) (some (0, 8, 4))
    (.next ([2689200000000, -5160000000000], [5975400000000, 2580000000000]) (some (0, 8, 4)) (some
    (0, 8, 4)) (.next ([335400000000, 2580000000000], [875400000000, 2580000000000]) (some (0, 8,
    4)) (some (8, 8, 4)) (.next ([1665000000000], [4365000000000]) (some (8, 8, 4)) (some (8, 8, 4))
    (.next ([1460400000000, 2580000000000], [4700400000000, 2580000000000]) (some (8, 8, 4)) (some
    (8, 8, 4)) (.next ([1125000000000], [4500000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next
    ([1095000000000], [4500000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next ([930000000000],
    [4875000000000]) (some (8, 8, 4)) (some (8, 8, 5)) (.next ([900000000000], [4875000000000])
    (some (8, 8, 5)) (some (8, 8, 5)) (.next ([789600000000, -2580000000000], [5035800000000,
    5160000000000]) (some (8, 8, 5)) (some (8, 8, 5)) (.next ([725400000000, 2580000000000],
    [5210400000000, 2580000000000]) (some (8, 8, 5)) (some (8, 8, 5)) (.next ([695400000000,
    2580000000000], [5210400000000, 2580000000000]) (some (8, 8, 5)) (some (8, 8, 5)) (.next
    ([454200000000, -5160000000000], [4700400000000, 2580000000000]) (some (8, 8, 5)) (some (8, 8,
    5)) (.next ([54600000000, -2580000000000], [5545800000000, 5160000000000]) (some (8, 8, 5))
    (some (8, 8, 5)) (.next ([24600000000, -2580000000000], [5545800000000, 5160000000000]) (some
    (8, 8, 5)) (some (8, 8, 5)) (.next ([-150000000000], [7875000000000]) (some (8, 8, 5)) (some (8,
    8, 5)) (.next ([-375000000000], [8610000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next
    ([-405000000000], [8640000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([-280800000000,
    -5160000000000], [5210400000000, 2580000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next
    ([-310800000000, -5160000000000], [5210400000000, 2580000000000]) (some (8, 2, 5)) (some (8, 2,
    5)) fan14Owner0Part0))))))))))))))))))))))))

theorem excluded8_1 : ExcludedOn (model8.B 1 ++ [step8.q]) 9000000000000 (model8.caps 1) (model8.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000], [4065000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([1170000000000, 9000000000000], [1170000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([4125000000000], [5235000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([2955000000000, -9000000000000], [6405000000000,
      9000000000000]) (some (0, 3, 2)) none (.next ([0, 0], [1170000000000, 9000000000000]) none
      none (.next ([-4065000000000, 9000000000000], [8190000000000, -9000000000000]) (some (3, 3,
      0)) (some (3, 3, 0)) (.next ([-1170000000000, -9000000000000], [2340000000000,
      18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-5235000000000], [9360000000000])
      (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-6405000000000, -9000000000000], [9360000000000,
      0]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3,
      1, 0))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6045000000000, 9000000000000], [2595000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([4875000000000], [3765000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([1800000000000], [1965000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([1170000000000, 9000000000000], [6840000000000, 0]) (some (0, 1, 2))
      (some (0, 1, 3)) (.next ([0, 0], [1170000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([-2595000000000, 9000000000000], [8640000000000, 0]) (some (0, 1, 3)) (some (0, 2,
      3)) (.next ([-3765000000000], [8640000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-1965000000000], [3765000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-6840000000000,
      0], [8010000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_6 : ExcludedOn (model8.B 6 ++ [step8.q]) 9000000000000 (model8.caps 6) (model8.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3765000000000], [360000000000]) (some (2, 0, 1))
      (some (2, 0, 2)) (.next ([4125000000000], [4065000000000, -9000000000000]) (some (2, 0, 2))
      (some (2, 0, 2)) (.next ([810000000000, 9000000000000], [2955000000000, -9000000000000]) (some
      (2, 0, 2)) (some (3, 0, 2)) (.next ([1170000000000, 9000000000000], [7830000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1170000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-360000000000], [4125000000000])
      (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-4065000000000, 9000000000000], [8190000000000,
      -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2955000000000, 9000000000000],
      [3765000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-7830000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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

theorem excluded9_0 : ExcludedOn (model9.B 0 ++ [step9.q]) 9000000000000 (model9.caps 0) (model9.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_1 : ExcludedOn (model9.B 1 ++ [step9.q]) 9000000000000 (model9.caps 1) (model9.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_2 : ExcludedOn (model9.B 2 ++ [step9.q]) 9000000000000 (model9.caps 2) (model9.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_3 : ExcludedOn (model9.B 3 ++ [step9.q]) 9000000000000 (model9.caps 3) (model9.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_4 : ExcludedOn (model9.B 4 ++ [step9.q]) 9000000000000 (model9.caps 4) (model9.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded9_6
    · exact excluded9_7
    · exact (hj rfl).elim
    · exact excluded9_9
theorem next9 : model9.insert step9 = model10 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded10_0 : ExcludedOn (model10.B 0 ++ [step10.q]) 9000000000000 (model10.caps 0)
    (model10.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_1 : ExcludedOn (model10.B 1 ++ [step10.q]) 9000000000000 (model10.caps 1)
    (model10.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_2 : ExcludedOn (model10.B 2 ++ [step10.q]) 9000000000000 (model10.caps 2)
    (model10.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_4 : ExcludedOn (model10.B 4 ++ [step10.q]) 9000000000000 (model10.caps 4)
    (model10.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_8 : ExcludedOn (model10.B 8 ++ [step10.q]) 9000000000000 (model10.caps 8)
    (model10.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6645000000000], [999000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([1170000000000, 9000000000000], [1935000000000, -9000000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2106000000000, 0], [6474000000000, -9000000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2106000000000], [7644000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([0], [3105000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-999000000000], [7644000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1935000000000,
      9000000000000], [3105000000000]) (some (0, 1, 3)) (some (0, 3, 3)) (.next ([-6474000000000,
      9000000000000], [8580000000000, -9000000000000]) (some (0, 3, 3)) (some (0, 3, 3)) (.next
      ([-7644000000000], [9750000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some (0, 3,
      2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded10_2
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 2 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_1 : ExcludedOn (model11.B 1 ++ [step11.q]) 9000000000000 (model11.caps 1)
    (model11.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_2 : ExcludedOn (model11.B 2 ++ [step11.q]) 9000000000000 (model11.caps 2)
    (model11.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8064000000000, 9000000000000], [1455000000000,
      -9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([6894000000000], [2625000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([5724000000000, -9000000000000], [2625000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1170000000000, 9000000000000], [1170000000000,
      9000000000000]) (some (0, 3, 1)) (some (3, 3, 1)) (.next ([0, 0], [1170000000000,
      9000000000000]) (some (3, 3, 1)) (some (3, 3, 1)) (.next ([-1455000000000, 9000000000000],
      [9519000000000, 0]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([-2625000000000],
      [9519000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2625000000000, 0],
      [8349000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1170000000000,
      -9000000000000], [2340000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal
      (some (3, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded11_4 : ExcludedOn (model11.B 4 ++ [step11.q]) 9000000000000 (model11.caps 4)
    (model11.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4929600000000, -2580000000000], [280800000000,
      5160000000000]) (some (7, 8, 3)) (some (7, 8, 4)) (.next ([4899600000000, -2580000000000],
      [310800000000, 5160000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([4839600000000,
      -2580000000000], [444600000000, -2580000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next
      ([5550000000000], [1140000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([4504200000000,
      -5160000000000], [1115400000000, 2580000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next
      ([4839600000000, -2580000000000], [1450800000000, 5160000000000]) (some (7, 8, 4)) (some (7,
      8, 4)) (.next ([510000000000], [225000000000]) (some (7, 8, 4)) (some (8, 8, 4))
      fan12Owner0Part1))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5436000000000], [1719000000000]) (some (3, 5,
      5)) (some (4, 5, 5)) (.next ([7125000000000, 9000000000000], [2655000000000, -9000000000000])
      (some (4, 5, 2)) (some (4, 5, 2)) (.next ([1455000000000, -9000000000000], [651000000000,
      9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([1356000000000], [750000000000])
      (some (4, 5, 2)) (some (4, 5, 3)) (.next ([5955000000000], [3825000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([4599000000000], [3075000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([4785000000000, -9000000000000], [3825000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([1170000000000, 9000000000000], [1170000000000, 9000000000000]) (some (4, 5, 3)) (some
      (4, 5, 3)) (.next ([519000000000], [837000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([519000000000], [2106000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([420000000000,
      9000000000000], [2106000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0],
      [1170000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([-1719000000000],
      [7155000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2655000000000, 9000000000000],
      [9780000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-651000000000, -9000000000000],
      [2106000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-750000000000], [2106000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3825000000000], [9780000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-3075000000000], [7674000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-3825000000000], [8610000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-1170000000000, -9000000000000], [2340000000000, 18000000000000]) (some (0, 5, 3))
      (some (5, 5, 3)) (.next ([-837000000000], [1356000000000]) (some (5, 5, 3)) (some (5, 5, 3))
      (.next ([-2106000000000], [2625000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next
      ([-2106000000000, 0], [2526000000000, 9000000000000]) (some (5, 5, 3)) (some (5, 5, 3))
      (.terminal (some (5, 5, 3)) (some (5, 5, 3)) (some (5, 5, 3))))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded12_5 : ExcludedOn (model12.B 5 ++ [step12.q]) 9000000000000 (model12.caps 5)
    (model12.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_6 : ExcludedOn (model12.B 6 ++ [step12.q]) 9000000000000 (model12.caps 6)
    (model12.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded12_5
    · exact excluded12_6
    · exact excluded12_7
    · exact excluded12_8
    · exact excluded12_9
theorem next12 : model12.insert step12 = model13 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded13_0 : ExcludedOn (model13.B 0 ++ [step13.q]) 9000000000000 (model13.caps 0)
    (model13.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4929600000000, -2580000000000], [280800000000,
      5160000000000]) (some (7, 8, 3)) (some (7, 8, 4)) (.next ([4899600000000, -2580000000000],
      [310800000000, 5160000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([670800000000,
      5160000000000], [204600000000, -2580000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next
      ([510000000000], [225000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([510000000000],
      [255000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([710400000000, 2580000000000],
      [695400000000, 2580000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([335400000000,
      2580000000000], [335400000000, 2580000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next
      ([180000000000], [195000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([3885000000000],
      [5475000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([3174600000000, -2580000000000],
      [4779600000000, -2580000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([3510000000000],
      [5655000000000]) (some (0, 8, 4)) (some (0, 8, 4)) fan13Owner0Part1)))))))))))) (den :=
      9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_1 : ExcludedOn (model13.B 1 ++ [step13.q]) 9000000000000 (model13.caps 1)
    (model13.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_2 : ExcludedOn (model13.B 2 ++ [step13.q]) 9000000000000 (model13.caps 2)
    (model13.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_3 : ExcludedOn (model13.B 3 ++ [step13.q]) 9000000000000 (model13.caps 3)
    (model13.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_5 : ExcludedOn (model13.B 5 ++ [step13.q]) 9000000000000 (model13.caps 5)
    (model13.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded13_0
    · exact excluded13_1
    · exact excluded13_2
    · exact excluded13_3
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7725000000000], [150000000000]) (some (7, 8, 3))
      (some (7, 8, 4)) (.next ([8235000000000], [375000000000]) (some (7, 8, 4)) (some (7, 8, 4))
      (.next ([8235000000000], [405000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next
      ([4929600000000, -2580000000000], [280800000000, 5160000000000]) (some (7, 8, 4)) (some (7, 8,
      4)) (.next ([4899600000000, -2580000000000], [310800000000, 5160000000000]) (some (7, 8, 4))
      (some (7, 8, 4)) (.next ([670800000000, 5160000000000], [204600000000, -2580000000000]) (some
      (7, 8, 4)) (some (7, 8, 4)) (.next ([510000000000], [225000000000]) (some (7, 8, 4)) (some (7,
      8, 4)) (.next ([510000000000], [255000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next
      ([710400000000, 2580000000000], [695400000000, 2580000000000]) (some (7, 8, 4)) (some (7, 8,
      4)) (.next ([335400000000, 2580000000000], [335400000000, 2580000000000]) (some (7, 8, 4))
      (some (7, 8, 4)) (.next ([180000000000], [195000000000]) (some (0, 8, 4)) (some (0, 8, 4))
      fan14Owner0Part1))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_5 : ExcludedOn (model14.B 5 ++ [step14.q]) 9000000000000 (model14.caps 5)
    (model14.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_6 : ExcludedOn (model14.B 6 ++ [step14.q]) 9000000000000 (model14.caps 6)
    (model14.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded14_2
    · exact excluded14_3
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([1455000000000, -9000000000000], [651000000000,
      9000000000000]) (some (3, 5, 2)) (some (5, 5, 2)) (.next ([1356000000000], [750000000000])
      (some (5, 5, 2)) (some (5, 5, 3)) (.next ([1170000000000, 9000000000000], [1170000000000,
      9000000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next ([519000000000], [837000000000])
      (some (5, 5, 3)) (some (5, 5, 3)) (.next ([2625000000000], [6375000000000]) (some (5, 5, 3))
      (some (5, 5, 3)) (.next ([2106000000000], [5538000000000]) (some (5, 2, 3)) (some (5, 2, 3))
      (.next ([519000000000], [2106000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([420000000000, 9000000000000], [2106000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([0], [1170000000000, 9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-651000000000, -9000000000000], [2106000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-750000000000], [2106000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-1170000000000,
      -9000000000000], [2340000000000, 18000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-837000000000], [1356000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-6375000000000],
      [9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-5538000000000], [7644000000000])
      (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-2106000000000], [2625000000000]) (some (5, 2, 3))
      (some (5, 2, 3)) (.next ([-2106000000000, 0], [2526000000000, 9000000000000]) (some (5, 2, 3))
      (some (5, 2, 3)) (.terminal (some (5, 2, 3)) (some (5, 2, 3)) (some (5, 2,
      3))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded15_4 : ExcludedOn (model15.B 4 ++ [step15.q]) 9000000000000 (model15.caps 4)
    (model15.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded15_2
    · exact excluded15_3
    · exact excluded15_4
    · exact excluded15_5
    · exact excluded15_6
    · exact excluded15_7
    · exact (hj rfl).elim
    · exact excluded15_9
theorem next15 : model15.insert step15 = model16 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext130000140000
end ConwaySoifer.Simplified.Certificates
