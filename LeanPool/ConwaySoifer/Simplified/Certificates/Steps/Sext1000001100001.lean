/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext100000110000
import Mathlib.Tactic.FinCases

/-!
# Sext 100000 110000 1

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
def fan8Owner0Part0 : FanWitness := (.next ([366000000000, -5340000000000], [5517000000000,
    2670000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([183000000000, -2670000000000],
    [6084000000000, 5340000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([0, 0], [801000000000,
    8010000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-84000000000, -5340000000000],
    [5817000000000, 2670000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-633000000000,
    2670000000000], [5091000000000, -5340000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-1167000000000, -2670000000000], [6159000000000, 5340000000000]) (some (7, 3, 5)) (some (7, 3,
    5)) (.next ([-1167000000000, -2670000000000], [5358000000000, -2670000000000]) (some (7, 3, 5))
    (some (7, 3, 5)) (.next ([-1434000000000, -5340000000000], [5892000000000, 2670000000000]) (some
    (7, 3, 5)) (some (7, 3, 5)) (.next ([-150000000000], [450000000000]) (some (7, 3, 5)) (some (7,
    3, 5)) (.next ([-450000000000], [1050000000000]) (some (7, 3, 5)) (some (7, 4, 5)) (.next
    ([-4725000000000], [9975000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-267000000000,
    -2670000000000], [534000000000, 5340000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next
    ([-5175000000000], [10275000000000]) (some (7, 4, 5)) (some (7, 4, 6)) (.next ([-4725000000000],
    [9225000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-4233000000000, 2670000000000],
    [5667000000000, 2670000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-4983000000000,
    2670000000000], [6417000000000, 2670000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-4767000000000, -2670000000000], [5934000000000, 5340000000000]) (some (7, 4, 6)) (some (7, 4,
    6)) (.next ([-5517000000000, -2670000000000], [6684000000000, 5340000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-5283000000000, 2670000000000], [6267000000000, 2670000000000]) (some
    (7, 4, 6)) (some (7, 4, 6)) (.next ([-5817000000000, -2670000000000], [6534000000000,
    5340000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5784000000000, -5340000000000],
    [6417000000000, 2670000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-4767000000000,
    -2670000000000], [5133000000000, -2670000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-5517000000000, -2670000000000], [5883000000000, -2670000000000]) (some (7, 4, 6)) (some (7,
    4, 6)) (.next ([-6084000000000, -5340000000000], [6267000000000, 2670000000000]) (some (7, 4,
    6)) (some (7, 4, 6)) (.terminal (some (7, 4, 6)) (some (7, 4, 6)) (some (7, 4,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan9Owner0Part0 : FanWitness := (.next ([717000000000, 2670000000000], [5817000000000,
    2670000000000]) (some (7, 7, 4)) (some (7, 7, 5)) (.next ([633000000000, -2670000000000],
    [5784000000000, 5340000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([366000000000,
    -5340000000000], [4767000000000, 2670000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next
    ([366000000000, -5340000000000], [5517000000000, 2670000000000]) (some (7, 7, 5)) (some (7, 7,
    5)) (.next ([183000000000, -2670000000000], [6084000000000, 5340000000000]) (some (7, 7, 5))
    (some (7, 7, 5)) (.next ([0, 0], [801000000000, 8010000000000]) (some (7, 7, 5)) (some (7, 7,
    5)) (.next ([-150000000000], [8550000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-750000000000], [8100000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-150000000000],
    [450000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-450000000000], [1050000000000])
    (some (7, 3, 5)) (some (7, 4, 5)) (.next ([-267000000000, -2670000000000], [534000000000,
    5340000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-6417000000000, -2670000000000],
    [9534000000000, 5340000000000]) (some (7, 4, 5)) (some (7, 4, 6)) (.next ([-5883000000000,
    2670000000000], [8466000000000, -5340000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-6684000000000, -5340000000000], [9267000000000, 2670000000000]) (some (7, 4, 6)) (some (7, 4,
    6)) (.next ([-6417000000000, -2670000000000], [8733000000000, -2670000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-4983000000000, 2670000000000], [6417000000000, 2670000000000]) (some
    (7, 4, 6)) (some (7, 4, 6)) (.next ([-4767000000000, -2670000000000], [5934000000000,
    5340000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5517000000000, -2670000000000],
    [6684000000000, 5340000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5283000000000,
    2670000000000], [6267000000000, 2670000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-5817000000000, -2670000000000], [6534000000000, 5340000000000]) (some (7, 4, 6)) (some (7, 4,
    6)) (.next ([-5784000000000, -5340000000000], [6417000000000, 2670000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-4767000000000, -2670000000000], [5133000000000, -2670000000000])
    (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5517000000000, -2670000000000], [5883000000000,
    -2670000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-6084000000000, -5340000000000],
    [6267000000000, 2670000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.terminal (some (7, 4, 6))
    (some (7, 4, 6)) (some (7, 4, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner0Part0 : FanWitness := (.next ([366000000000, -5340000000000], [5517000000000,
    2670000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([366000000000, -5340000000000],
    [8142000000000, 2670000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([183000000000,
    -2670000000000], [6084000000000, 5340000000000]) (some (0, 7, 5)) (some (7, 7, 5)) (.next ([0,
    0], [801000000000, 8010000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([-84000000000,
    -5340000000000], [5817000000000, 2670000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next
    ([-1725000000000], [7875000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([-1875000000000],
    [8325000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-2475000000000], [7875000000000])
    (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-150000000000], [450000000000]) (some (7, 3, 5))
    (some (7, 3, 5)) (.next ([-450000000000], [1050000000000]) (some (7, 3, 5)) (some (7, 4, 5))
    (.next ([-267000000000, -2670000000000], [534000000000, 5340000000000]) (some (7, 4, 5)) (some
    (7, 4, 5)) (.next ([-4233000000000, 2670000000000], [5667000000000, 2670000000000]) (some (7, 4,
    5)) (some (7, 4, 6)) (.next ([-4983000000000, 2670000000000], [6417000000000, 2670000000000])
    (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-4767000000000, -2670000000000], [5934000000000,
    5340000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5517000000000, -2670000000000],
    [6684000000000, 5340000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5283000000000,
    2670000000000], [6267000000000, 2670000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-8142000000000, -2670000000000], [9309000000000, 5340000000000]) (some (7, 4, 6)) (some (7, 4,
    6)) (.next ([-5817000000000, -2670000000000], [6534000000000, 5340000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-5784000000000, -5340000000000], [6417000000000, 2670000000000]) (some
    (7, 4, 6)) (some (7, 4, 6)) (.next ([-7608000000000, 2670000000000], [8241000000000,
    -5340000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-8409000000000, -5340000000000],
    [9042000000000, 2670000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5517000000000,
    -2670000000000], [5883000000000, -2670000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-8142000000000, -2670000000000], [8508000000000, -2670000000000]) (some (7, 4, 6)) (some (7,
    4, 6)) (.next ([-6084000000000, -5340000000000], [6267000000000, 2670000000000]) (some (7, 4,
    6)) (some (7, 4, 6)) (.terminal (some (7, 4, 6)) (some (7, 4, 6)) (some (7, 4,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner0Part0 : FanWitness := (.next ([366000000000, -5340000000000], [5517000000000,
    2670000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([291000000000, -5340000000000],
    [8067000000000, 2670000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([183000000000,
    -2670000000000], [6084000000000, 5340000000000]) (some (0, 7, 5)) (some (7, 7, 5)) (.next ([0,
    0], [801000000000, 8010000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([-84000000000,
    -5340000000000], [5817000000000, 2670000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next
    ([-1650000000000], [7725000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([-1800000000000],
    [8175000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-2400000000000], [7725000000000])
    (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-150000000000], [450000000000]) (some (7, 3, 5))
    (some (7, 3, 5)) (.next ([-450000000000], [1050000000000]) (some (7, 3, 5)) (some (7, 4, 5))
    (.next ([-267000000000, -2670000000000], [534000000000, 5340000000000]) (some (7, 4, 5)) (some
    (7, 4, 5)) (.next ([-4233000000000, 2670000000000], [5667000000000, 2670000000000]) (some (7, 4,
    5)) (some (7, 4, 6)) (.next ([-4983000000000, 2670000000000], [6417000000000, 2670000000000])
    (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-4767000000000, -2670000000000], [5934000000000,
    5340000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5517000000000, -2670000000000],
    [6684000000000, 5340000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5283000000000,
    2670000000000], [6267000000000, 2670000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-8067000000000, -2670000000000], [9159000000000, 5340000000000]) (some (7, 4, 6)) (some (7, 4,
    6)) (.next ([-5817000000000, -2670000000000], [6534000000000, 5340000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-5784000000000, -5340000000000], [6417000000000, 2670000000000]) (some
    (7, 4, 6)) (some (7, 4, 6)) (.next ([-7533000000000, 2670000000000], [8091000000000,
    -5340000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-8334000000000, -5340000000000],
    [8892000000000, 2670000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5517000000000,
    -2670000000000], [5883000000000, -2670000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-8067000000000, -2670000000000], [8358000000000, -2670000000000]) (some (7, 4, 6)) (some (7,
    4, 6)) (.next ([-6084000000000, -5340000000000], [6267000000000, 2670000000000]) (some (7, 4,
    6)) (some (7, 4, 6)) (.terminal (some (7, 4, 6)) (some (7, 4, 6)) (some (7, 4,
    6)))))))))))))))))))))))))))

theorem excluded8_0 : ExcludedOn (model8.B 0 ++ [step8.q]) 9000000000000 (model8.caps 0) (model8.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5733000000000, -2670000000000], [84000000000,
      5340000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([4458000000000, -2670000000000],
      [633000000000, -2670000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([4992000000000,
      2670000000000], [1167000000000, 2670000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([4191000000000, -5340000000000], [1167000000000, 2670000000000]) (some (6, 7, 4)) (some (6,
      7, 4)) (.next ([4458000000000, -2670000000000], [1434000000000, 5340000000000]) (some (6, 7,
      4)) (some (6, 7, 4)) (.next ([300000000000], [150000000000]) (some (6, 7, 4)) (some (7, 7, 4))
      (.next ([600000000000], [450000000000]) (some (7, 7, 4)) (some (7, 7, 4)) (.next
      ([5250000000000], [4725000000000]) (some (7, 7, 4)) (some (7, 7, 4)) (.next ([267000000000,
      2670000000000], [267000000000, 2670000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next
      ([5100000000000], [5175000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([4500000000000],
      [4725000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([1434000000000, 5340000000000],
      [4233000000000, -2670000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([1434000000000,
      5340000000000], [4983000000000, -2670000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next
      ([1167000000000, 2670000000000], [4767000000000, 2670000000000]) (some (7, 3, 4)) (some (7, 3,
      4)) (.next ([1167000000000, 2670000000000], [5517000000000, 2670000000000]) (some (7, 3, 4))
      (some (7, 3, 4)) (.next ([984000000000, 5340000000000], [5283000000000, -2670000000000]) (some
      (7, 3, 4)) (some (7, 3, 4)) (.next ([717000000000, 2670000000000], [5817000000000,
      2670000000000]) (some (7, 3, 4)) (some (7, 3, 5)) (.next ([633000000000, -2670000000000],
      [5784000000000, 5340000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([366000000000,
      -5340000000000], [4767000000000, 2670000000000]) (some (7, 3, 5)) (some (7, 3, 5))
      fan8Owner0Part0)))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_1 : ExcludedOn (model8.B 1 ++ [step8.q]) 9000000000000 (model8.caps 1) (model8.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_2 : ExcludedOn (model8.B 2 ++ [step8.q]) 9000000000000 (model8.caps 2) (model8.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_3 : ExcludedOn (model8.B 3 ++ [step8.q]) 9000000000000 (model8.caps 3) (model8.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1350000000000, 9000000000000], [600000000000,
      -9000000000000]) (some (2, 4, 4)) (some (3, 4, 4)) (.next ([6525000000000, 9000000000000],
      [3375000000000, -9000000000000]) (some (3, 4, 4)) (some (3, 4, 4)) (.next ([5175000000000],
      [2775000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([5625000000000], [4275000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([4725000000000, -9000000000000], [4275000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([900000000000, 9000000000000], [900000000000,
      9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([450000000000], [1500000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0], [900000000000, 9000000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([-600000000000, 9000000000000], [1950000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-3375000000000, 9000000000000], [9900000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-2775000000000], [7950000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([-4275000000000], [9900000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-4275000000000], [9000000000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-900000000000, -9000000000000], [1800000000000, 18000000000000]) (some (0, 4, 2)) (some (4,
      4, 2)) (.next ([-1500000000000], [1950000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.terminal
      (some (4, 4, 2)) (some (4, 4, 2)) (some (4, 4, 2))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_5 : ExcludedOn (model8.B 5 ++ [step8.q]) 9000000000000 (model8.caps 5) (model8.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_6 : ExcludedOn (model8.B 6 ++ [step8.q]) 9000000000000 (model8.caps 6) (model8.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded8_0
    · exact excluded8_1
    · exact excluded8_2
    · exact excluded8_3
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.witnessedFan (.next ([8400000000000], [150000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([7350000000000], [750000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([300000000000], [150000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([600000000000], [450000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([267000000000,
      2670000000000], [267000000000, 2670000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([3117000000000, 2670000000000], [6417000000000, 2670000000000]) (some (0, 7, 4)) (some (0, 7,
      4)) (.next ([2583000000000, -2670000000000], [5883000000000, -2670000000000]) (some (0, 7, 4))
      (some (0, 7, 4)) (.next ([2583000000000, -2670000000000], [6684000000000, 5340000000000])
      (some (0, 7, 4)) (some (0, 7, 4)) (.next ([2316000000000, -5340000000000], [6417000000000,
      2670000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([1434000000000, 5340000000000],
      [4983000000000, -2670000000000]) (some (0, 7, 4)) (some (7, 7, 4)) (.next ([1167000000000,
      2670000000000], [4767000000000, 2670000000000]) (some (7, 7, 4)) (some (7, 7, 4)) (.next
      ([1167000000000, 2670000000000], [5517000000000, 2670000000000]) (some (7, 7, 4)) (some (7, 7,
      4)) (.next ([984000000000, 5340000000000], [5283000000000, -2670000000000]) (some (7, 7, 4))
      (some (7, 7, 4)) fan9Owner0Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_5 : ExcludedOn (model9.B 5 ++ [step9.q]) 9000000000000 (model9.caps 5) (model9.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_1 : ExcludedOn (model10.B 1 ++ [step10.q]) 9000000000000 (model10.caps 1)
    (model10.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_2 : ExcludedOn (model10.B 2 ++ [step10.q]) 9000000000000 (model10.caps 2)
    (model10.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_3 : ExcludedOn (model10.B 3 ++ [step10.q]) 9000000000000 (model10.caps 3)
    (model10.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1350000000000, 9000000000000], [600000000000,
      -9000000000000]) (some (2, 4, 1)) (some (4, 4, 1)) (.next ([900000000000, 9000000000000],
      [900000000000, 9000000000000]) (some (4, 4, 1)) (some (4, 4, 2)) (.next ([450000000000],
      [1500000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([1950000000000], [7200000000000])
      (some (4, 4, 2)) (some (4, 4, 2)) (.next ([900000000000, 9000000000000], [6750000000000,
      -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0], [900000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-600000000000, 9000000000000], [1950000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-900000000000, -9000000000000], [1800000000000,
      18000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-1500000000000], [1950000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-7200000000000], [9150000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([-6750000000000, 9000000000000], [7650000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.terminal (some (4, 1, 2)) (some (4, 1, 2)) (some (4, 1, 2)))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded10_4 : ExcludedOn (model10.B 4 ++ [step10.q]) 9000000000000 (model10.caps 4)
    (model10.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded10_3
    · exact excluded10_4
    · exact excluded10_5
    · exact excluded10_6
    · exact excluded10_7
    · exact (hj rfl).elim
    · exact excluded10_9
theorem next10 : model10.insert step10 = model11 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded11_0 : ExcludedOn (model11.B 0 ++ [step11.q]) 9000000000000 (model11.caps 0)
    (model11.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_1 : ExcludedOn (model11.B 1 ++ [step11.q]) 9000000000000 (model11.caps 1)
    (model11.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_2 : ExcludedOn (model11.B 2 ++ [step11.q]) 9000000000000 (model11.caps 2)
    (model11.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_3 : ExcludedOn (model11.B 3 ++ [step11.q]) 9000000000000 (model11.caps 3)
    (model11.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7800000000000], [750000000000]) (some (2, 4, 1))
      (some (3, 4, 1)) (.next ([6300000000000], [1800000000000, -9000000000000]) (some (3, 4, 1))
      (some (3, 4, 1)) (.next ([7200000000000, 9000000000000], [2700000000000]) (some (3, 4, 1))
      (some (3, 4, 1)) (.next ([6300000000000], [2700000000000]) (some (3, 4, 1)) (some (3, 4, 2))
      (.next ([1050000000000, -9000000000000], [450000000000, 9000000000000]) (some (3, 4, 2)) (some
      (4, 4, 2)) (.next ([900000000000, 9000000000000], [900000000000, 9000000000000]) (some (4, 4,
      2)) (some (4, 4, 2)) (.next ([450000000000], [1500000000000]) (some (4, 4, 2)) (some (4, 4,
      2)) (.next ([0], [900000000000, 9000000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next
      ([-750000000000], [8550000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([-1800000000000,
      9000000000000], [8100000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-2700000000000, 0], [9900000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-2700000000000], [9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-450000000000,
      -9000000000000], [1500000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-900000000000,
      -9000000000000], [1800000000000, 18000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-1500000000000], [1950000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.terminal (some (4, 1,
      2)) (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded11_4 : ExcludedOn (model11.B 4 ++ [step11.q]) 9000000000000 (model11.caps 4)
    (model11.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded11_7
    · exact (hj rfl).elim
    · exact excluded11_9
theorem next11 : model11.insert step11 = model12 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded12_0 : ExcludedOn (model12.B 0 ++ [step12.q]) 9000000000000 (model12.caps 0)
    (model12.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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

theorem excluded12_4 : ExcludedOn (model12.B 4 ++ [step12.q]) 9000000000000 (model12.caps 4)
    (model12.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000], [1875000000000]) (some (4, 0,
      1)) (some (4, 1, 1)) (.next ([4500000000000], [5025000000000]) (some (4, 1, 1)) (some (4, 1,
      2)) (.next ([1800000000000, 9000000000000], [2475000000000, -9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([1125000000000], [2475000000000, -9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([1125000000000], [3150000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([1125000000000], [3375000000000]) (some (3, 1, 2)) (some (3, 1, 4)) (.next
      ([900000000000], [3375000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([900000000000,
      9000000000000], [6150000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0],
      [6150000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([-1875000000000], [5250000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-5025000000000], [9525000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-2475000000000, 9000000000000], [4275000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-2475000000000, 9000000000000], [3600000000000, -9000000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-3150000000000], [4275000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-3375000000000], [4500000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-3375000000000], [4275000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-6150000000000], [7050000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.terminal (some (0, 1, 4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_8 : ExcludedOn (model12.B 8 ++ [step12.q]) 9000000000000 (model12.caps 8)
    (model12.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5625000000000], [3150000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([5625000000000], [4500000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([1350000000000], [1350000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([2925000000000], [4500000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [2700000000000]) (some (0, 1, 3)) (some (0, 3, 3)) (.next ([-3150000000000], [8775000000000])
      (some (0, 3, 3)) (some (0, 3, 3)) (.next ([-4500000000000], [10125000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-1350000000000], [2700000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-4500000000000], [7425000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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

theorem excluded13_0 : ExcludedOn (model13.B 0 ++ [step13.q]) 9000000000000 (model13.caps 0)
    (model13.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_1 : ExcludedOn (model13.B 1 ++ [step13.q]) 9000000000000 (model13.caps 1)
    (model13.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_2 : ExcludedOn (model13.B 2 ++ [step13.q]) 9000000000000 (model13.caps 2)
    (model13.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5400000000000, 9000000000000], [4500000000000,
      -9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([900000000000, 9000000000000],
      [900000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4500000000000],
      [5400000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([3600000000000, -9000000000000],
      [5400000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0, 0], [900000000000,
      9000000000000]) (some (0, 3, 1)) (some (3, 3, 1)) (.next ([-4500000000000, 9000000000000],
      [9900000000000, 0]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([-900000000000, -9000000000000],
      [1800000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-5400000000000],
      [9900000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-5400000000000, 0],
      [9000000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2))
      (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_4 : ExcludedOn (model13.B 4 ++ [step13.q]) 9000000000000 (model13.caps 4)
    (model13.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5733000000000, -2670000000000], [84000000000,
      5340000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([6150000000000], [1725000000000])
      (some (6, 7, 4)) (some (6, 7, 4)) (.next ([6450000000000], [1875000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([5400000000000], [2475000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([300000000000], [150000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([600000000000], [450000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([267000000000,
      2670000000000], [267000000000, 2670000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([1434000000000, 5340000000000], [4233000000000, -2670000000000]) (some (0, 7, 4)) (some (0,
      7, 4)) (.next ([1434000000000, 5340000000000], [4983000000000, -2670000000000]) (some (0, 7,
      4)) (some (0, 7, 4)) (.next ([1167000000000, 2670000000000], [4767000000000, 2670000000000])
      (some (0, 7, 4)) (some (0, 7, 4)) (.next ([1167000000000, 2670000000000], [5517000000000,
      2670000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([984000000000, 5340000000000],
      [5283000000000, -2670000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([1167000000000,
      2670000000000], [8142000000000, 2670000000000]) (some (0, 7, 4)) (some (0, 7, 5)) (.next
      ([717000000000, 2670000000000], [5817000000000, 2670000000000]) (some (0, 7, 5)) (some (0, 7,
      5)) (.next ([633000000000, -2670000000000], [5784000000000, 5340000000000]) (some (0, 7, 5))
      (some (0, 7, 5)) (.next ([633000000000, -2670000000000], [7608000000000, -2670000000000])
      (some (0, 7, 5)) (some (0, 7, 5)) (.next ([633000000000, -2670000000000], [8409000000000,
      5340000000000]) (some (0, 7, 5)) (some (0, 7, 5)) fan14Owner0Part0))))))))))))))))))
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

theorem excluded14_4 : ExcludedOn (model14.B 4 ++ [step14.q]) 9000000000000 (model14.caps 4)
    (model14.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7875000000000], [225000000000]) (some (3, 0, 4))
      (some (3, 1, 4)) (.next ([1725000000000], [225000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([3375000000000], [1875000000000]) (some (3, 1, 4)) (some (3, 4, 4)) (.next
      ([3150000000000], [3825000000000]) (some (3, 4, 4)) (some (3, 4, 4)) (.next ([1800000000000,
      9000000000000], [2475000000000, -9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([900000000000], [3375000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([900000000000,
      9000000000000], [6150000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([675000000000,
      9000000000000], [8100000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0],
      [6150000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-225000000000], [8100000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-225000000000], [1950000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-1875000000000], [5250000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([-3825000000000], [6975000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-2475000000000, 9000000000000], [4275000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-3375000000000], [4275000000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next
      ([-6150000000000], [7050000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-8100000000000], [8775000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.terminal (some (0, 4, 3)) (some (0, 4, 3)) (some (0, 4, 3))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded14_6 : ExcludedOn (model14.B 6 ++ [step14.q]) 9000000000000 (model14.caps 6)
    (model14.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded14_4
    · exact (hj rfl).elim
    · exact excluded14_6
    · exact excluded14_7
    · exact excluded14_8
    · exact excluded14_9
theorem next14 : model14.insert step14 = model15 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded15_0 : ExcludedOn (model15.B 0 ++ [step15.q]) 9000000000000 (model15.caps 0)
    (model15.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5733000000000, -2670000000000], [84000000000,
      5340000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([6075000000000], [1650000000000])
      (some (6, 7, 4)) (some (6, 7, 4)) (.next ([6375000000000], [1800000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([5325000000000], [2400000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([300000000000], [150000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([600000000000], [450000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([267000000000,
      2670000000000], [267000000000, 2670000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([1434000000000, 5340000000000], [4233000000000, -2670000000000]) (some (0, 7, 4)) (some (0,
      7, 4)) (.next ([1434000000000, 5340000000000], [4983000000000, -2670000000000]) (some (0, 7,
      4)) (some (0, 7, 4)) (.next ([1167000000000, 2670000000000], [4767000000000, 2670000000000])
      (some (0, 7, 4)) (some (0, 7, 4)) (.next ([1167000000000, 2670000000000], [5517000000000,
      2670000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([984000000000, 5340000000000],
      [5283000000000, -2670000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([1092000000000,
      2670000000000], [8067000000000, 2670000000000]) (some (0, 7, 4)) (some (0, 7, 5)) (.next
      ([717000000000, 2670000000000], [5817000000000, 2670000000000]) (some (0, 7, 5)) (some (0, 7,
      5)) (.next ([633000000000, -2670000000000], [5784000000000, 5340000000000]) (some (0, 7, 5))
      (some (0, 7, 5)) (.next ([558000000000, -2670000000000], [7533000000000, -2670000000000])
      (some (0, 7, 5)) (some (0, 7, 5)) (.next ([558000000000, -2670000000000], [8334000000000,
      5340000000000]) (some (0, 7, 5)) (some (0, 7, 5)) fan15Owner0Part0))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_4 : ExcludedOn (model15.B 4 ++ [step15.q]) 9000000000000 (model15.caps 4)
    (model15.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7800000000000], [375000000000]) (some (3, 0, 4))
      (some (3, 1, 4)) (.next ([1650000000000], [375000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([3375000000000], [1875000000000]) (some (3, 1, 4)) (some (3, 4, 4)) (.next
      ([3000000000000], [3900000000000]) (some (3, 4, 4)) (some (3, 4, 4)) (.next ([900000000000],
      [3375000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([900000000000, 9000000000000],
      [6150000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([525000000000, 9000000000000],
      [8175000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0], [6150000000000]) (some (3, 4,
      2)) (some (3, 4, 2)) (.next ([-375000000000], [8175000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([-375000000000], [2025000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1875000000000], [5250000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-3900000000000], [6900000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-3375000000000], [4275000000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next
      ([-6150000000000], [7050000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-8175000000000], [8700000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.terminal (some (0, 4, 3)) (some (0, 4, 3)) (some (0, 4, 3))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded15_6 : ExcludedOn (model15.B 6 ++ [step15.q]) 9000000000000 (model15.caps 6)
    (model15.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_7 : ExcludedOn (model15.B 7 ++ [step15.q]) 9000000000000 (model15.caps 7)
    (model15.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded15_0
    · exact excluded15_1
    · exact excluded15_2
    · exact excluded15_3
    · exact excluded15_4
    · exact (hj rfl).elim
    · exact excluded15_6
    · exact excluded15_7
    · exact excluded15_8
    · exact excluded15_9
theorem next15 : model15.insert step15 = model16 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext100000110000
end ConwaySoifer.Simplified.Certificates
