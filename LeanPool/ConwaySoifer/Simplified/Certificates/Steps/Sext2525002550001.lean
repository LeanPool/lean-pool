/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext252500255000
import Mathlib.Tactic.FinCases

/-!
# Sext 252500 255000 1

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
namespace Sext252500255000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan12Owner0Part0 : FanWitness := (.next ([-1481250000000], [6731250000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-375000000000], [1653750000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-1481250000000], [6345000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1893750000000], [6768750000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1893750000000], [6382500000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-750000000000],
    [2272500000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-1136250000000], [3176250000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-761250000000], [2040000000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-1136250000000], [2790000000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-375000000000], [750000000000]) (some (10, 3, 6)) (some (10, 3, 10)) (.next
    ([-1653750000000], [2790000000000]) (some (10, 3, 10)) (some (10, 3, 10)) (.next
    ([-1278750000000], [2040000000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next
    ([-2040000000000], [3176250000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next ([-761250000000],
    [1136250000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next ([-1278750000000], [1653750000000])
    (some (1, 3, 10)) (some (1, 3, 10)) (.next ([-1511250000000], [1897500000000]) (some (1, 3, 10))
    (some (1, 3, 10)) (.next ([-5208750000000], [6000000000000]) (some (1, 3, 10)) (some (1, 3, 10))
    (.next ([-5595000000000], [6386250000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next
    ([-375000000000], [412500000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next ([-5246250000000],
    [5625000000000]) (some (1, 3, 10)) (some (1, 4, 10)) (.next ([-5632500000000], [6011250000000])
    (some (1, 4, 10)) (some (1, 4, 10)) (.next ([-6345000000000], [6761250000000]) (some (1, 4, 10))
    (some (1, 4, 10)) (.next ([-6731250000000], [6761250000000]) (some (1, 4, 10)) (some (1, 4, 10))
    (.next ([-6382500000000], [6386250000000]) (some (1, 4, 10)) (some (1, 4, 10)) (.terminal (some
    (1, 4, 10)) (some (1, 4, 10)) (some (1, 4, 10)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan12Owner0Part1 : FanWitness := (.next ([375000000000], [375000000000]) (some (10, 3, 4)) (some
    (10, 3, 4)) (.next ([1136250000000], [1653750000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next
    ([761250000000], [1278750000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([1136250000000],
    [2040000000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([375000000000], [761250000000])
    (some (10, 3, 4)) (some (10, 3, 4)) (.next ([375000000000], [1278750000000]) (some (10, 3, 4))
    (some (10, 3, 4)) (.next ([386250000000], [1511250000000]) (some (10, 3, 4)) (some (10, 3, 4))
    (.next ([791250000000], [5208750000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next
    ([791250000000], [5595000000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([37500000000],
    [375000000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([378750000000], [5246250000000])
    (some (10, 3, 4)) (some (10, 3, 4)) (.next ([378750000000], [5632500000000]) (some (10, 3, 4))
    (some (10, 3, 5)) (.next ([416250000000], [6345000000000]) (some (10, 3, 5)) (some (10, 3, 5))
    (.next ([30000000000], [6731250000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
    ([3750000000], [6382500000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([0],
    [1897500000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-345000000000], [8385000000000])
    (some (10, 3, 5)) (some (10, 3, 6)) (.next ([-382500000000], [6768750000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-757500000000], [8422500000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-720000000000], [7106250000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1106250000000], [7106250000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1132500000000], [7143750000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-386250000000],
    [1897500000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-1518750000000], [7143750000000])
    (some (10, 3, 6)) (some (10, 3, 6)) fan12Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan13Owner0Part0 : FanWitness := (.next ([-1893750000000], [6768750000000]) (some (0, 10, 6))
    (some (0, 10, 6)) (.next ([-1893750000000], [6382500000000]) (some (0, 10, 6)) (some (0, 10, 6))
    (.next ([-750000000000], [2272500000000]) (some (0, 10, 6)) (some (0, 10, 6)) (.next
    ([-4148250000000], [9000000000000]) (some (0, 10, 6)) (some (0, 10, 6)) (.next
    ([-4534500000000], [9386250000000]) (some (0, 10, 6)) (some (0, 10, 6)) (.next ([-375000000000],
    [750000000000]) (some (0, 10, 6)) (some (0, 10, 6)) (.next ([-5284500000000], [9761250000000])
    (some (0, 10, 6)) (some (1, 10, 7)) (.next ([-5670750000000], [9761250000000]) (some (1, 10, 7))
    (some (1, 10, 7)) (.next ([-6045750000000], [9386250000000]) (some (1, 10, 7)) (some (1, 10, 7))
    (.next ([-761250000000], [1136250000000]) (some (1, 10, 7)) (some (1, 10, 7)) (.next
    ([-6045750000000], [9000000000000]) (some (1, 10, 7)) (some (1, 10, 7)) (.next
    ([-5284500000000], [7863750000000]) (some (1, 10, 7)) (some (1, 10, 7)) (.next
    ([-5670750000000], [8250000000000]) (some (1, 10, 7)) (some (1, 10, 7)) (.next
    ([-3000000000000], [4060500000000]) (some (1, 10, 7)) (some (10, 10, 7)) (.next
    ([-3375000000000], [4473000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next
    ([-1511250000000], [1897500000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next
    ([-5208750000000], [6000000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next
    ([-5595000000000], [6386250000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-375000000000],
    [412500000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-5246250000000], [5625000000000])
    (some (10, 3, 7)) (some (10, 4, 7)) (.next ([-5632500000000], [6011250000000]) (some (10, 4, 7))
    (some (10, 4, 7)) (.next ([-6345000000000], [6761250000000]) (some (10, 4, 7)) (some (10, 4, 7))
    (.next ([-6731250000000], [6761250000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-6382500000000], [6386250000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.terminal (some (10, 4,
    7)) (some (10, 4, 7)) (some (10, 4, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan13Owner0Part1 : FanWitness := (.next ([375000000000], [761250000000]) (some (9, 10, 4)) (some
    (9, 10, 4)) (.next ([2954250000000], [6045750000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next
    ([2579250000000], [5284500000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next ([2579250000000],
    [5670750000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next ([1060500000000], [3000000000000])
    (some (9, 10, 4)) (some (9, 10, 4)) (.next ([1098000000000], [3375000000000]) (some (9, 10, 4))
    (some (9, 10, 4)) (.next ([386250000000], [1511250000000]) (some (9, 10, 4)) (some (9, 10, 4))
    (.next ([791250000000], [5208750000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next
    ([791250000000], [5595000000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next ([37500000000],
    [375000000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next ([378750000000], [5246250000000])
    (some (9, 10, 4)) (some (9, 10, 4)) (.next ([378750000000], [5632500000000]) (some (9, 10, 4))
    (some (9, 10, 5)) (.next ([416250000000], [6345000000000]) (some (9, 10, 5)) (some (9, 10, 5))
    (.next ([30000000000], [6731250000000]) (some (9, 10, 5)) (some (9, 10, 5)) (.next
    ([3750000000], [6382500000000]) (some (9, 10, 5)) (some (9, 10, 5)) (.next ([0],
    [1897500000000]) (some (9, 10, 5)) (some (9, 10, 5)) (.next ([-382500000000], [6768750000000])
    (some (0, 10, 5)) (some (0, 10, 6)) (.next ([-720000000000], [7106250000000]) (some (0, 10, 6))
    (some (0, 10, 6)) (.next ([-1106250000000], [7106250000000]) (some (0, 10, 6)) (some (0, 10, 6))
    (.next ([-1132500000000], [7143750000000]) (some (0, 10, 6)) (some (0, 10, 6)) (.next
    ([-386250000000], [1897500000000]) (some (0, 10, 6)) (some (0, 10, 6)) (.next ([-1518750000000],
    [7143750000000]) (some (0, 10, 6)) (some (0, 10, 6)) (.next ([-1481250000000], [6731250000000])
    (some (0, 10, 6)) (some (0, 10, 6)) (.next ([-1481250000000], [6345000000000]) (some (0, 10, 6))
    (some (0, 10, 6)) fan13Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner0Part0 : FanWitness := (.next ([-1893750000000], [6768750000000]) (some (0, 10, 6))
    (some (0, 10, 6)) (.next ([-1893750000000], [6382500000000]) (some (0, 10, 6)) (some (0, 10, 6))
    (.next ([-750000000000], [2272500000000]) (some (0, 10, 6)) (some (0, 10, 6)) (.next
    ([-4683750000000], [9375000000000]) (some (0, 10, 6)) (some (0, 10, 6)) (.next ([-375000000000],
    [750000000000]) (some (0, 10, 6)) (some (0, 10, 6)) (.next ([-5070000000000], [9761250000000])
    (some (0, 10, 6)) (some (1, 10, 7)) (.next ([-5820000000000], [10136250000000]) (some (1, 10,
    7)) (some (1, 10, 7)) (.next ([-6206250000000], [10136250000000]) (some (1, 10, 7)) (some (1,
    10, 7)) (.next ([-761250000000], [1136250000000]) (some (1, 10, 7)) (some (1, 10, 7)) (.next
    ([-6581250000000], [9761250000000]) (some (1, 10, 7)) (some (1, 10, 7)) (.next
    ([-6581250000000], [9375000000000]) (some (1, 10, 7)) (some (1, 10, 7)) (.next
    ([-5820000000000], [8238750000000]) (some (1, 10, 7)) (some (1, 10, 7)) (.next
    ([-6206250000000], [8625000000000]) (some (1, 10, 7)) (some (1, 10, 7)) (.next
    ([-1511250000000], [1897500000000]) (some (1, 10, 7)) (some (10, 10, 7)) (.next
    ([-3375000000000], [3900000000000]) (some (10, 10, 7)) (some (10, 10, 7)) (.next
    ([-5208750000000], [6000000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next
    ([-3750000000000], [4312500000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next
    ([-5595000000000], [6386250000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-375000000000],
    [412500000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-5246250000000], [5625000000000])
    (some (10, 3, 7)) (some (10, 4, 7)) (.next ([-5632500000000], [6011250000000]) (some (10, 4, 7))
    (some (10, 4, 7)) (.next ([-6345000000000], [6761250000000]) (some (10, 4, 7)) (some (10, 4, 7))
    (.next ([-6731250000000], [6761250000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-6382500000000], [6386250000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.terminal (some (10, 4,
    7)) (some (10, 4, 7)) (some (10, 4, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner0Part1 : FanWitness := (.next ([3180000000000], [6581250000000]) (some (9, 10, 4))
    (some (9, 10, 4)) (.next ([2793750000000], [6581250000000]) (some (9, 10, 4)) (some (9, 10, 4))
    (.next ([2418750000000], [5820000000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next
    ([2418750000000], [6206250000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next ([386250000000],
    [1511250000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next ([525000000000], [3375000000000])
    (some (9, 10, 4)) (some (9, 10, 4)) (.next ([791250000000], [5208750000000]) (some (9, 10, 4))
    (some (9, 10, 4)) (.next ([562500000000], [3750000000000]) (some (9, 10, 4)) (some (9, 10, 4))
    (.next ([791250000000], [5595000000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next
    ([37500000000], [375000000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next ([378750000000],
    [5246250000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next ([378750000000], [5632500000000])
    (some (9, 10, 4)) (some (9, 10, 5)) (.next ([416250000000], [6345000000000]) (some (9, 10, 5))
    (some (9, 10, 5)) (.next ([30000000000], [6731250000000]) (some (9, 10, 5)) (some (9, 10, 5))
    (.next ([3750000000], [6382500000000]) (some (9, 10, 5)) (some (9, 10, 5)) (.next ([0],
    [1897500000000]) (some (9, 10, 5)) (some (9, 10, 5)) (.next ([-382500000000], [6768750000000])
    (some (0, 10, 5)) (some (0, 10, 6)) (.next ([-720000000000], [7106250000000]) (some (0, 10, 6))
    (some (0, 10, 6)) (.next ([-1106250000000], [7106250000000]) (some (0, 10, 6)) (some (0, 10, 6))
    (.next ([-1132500000000], [7143750000000]) (some (0, 10, 6)) (some (0, 10, 6)) (.next
    ([-386250000000], [1897500000000]) (some (0, 10, 6)) (some (0, 10, 6)) (.next ([-1518750000000],
    [7143750000000]) (some (0, 10, 6)) (some (0, 10, 6)) (.next ([-1481250000000], [6731250000000])
    (some (0, 10, 6)) (some (0, 10, 6)) (.next ([-1481250000000], [6345000000000]) (some (0, 10, 6))
    (some (0, 10, 6)) fan14Owner0Part0))))))))))))))))))))))))

theorem excluded8_1 : ExcludedOn (model8.B 1 ++ [step8.q]) 9000000000000 (model8.caps 1) (model8.ord
    1) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2272500000000, 9000000000000], [2272500000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([3030000000000], [3352500000000,
      -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([3030000000000], [5625000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([757500000000, -9000000000000], [7897500000000,
      9000000000000]) (some (0, 3, 2)) none (.next ([0, 0], [2272500000000, 9000000000000]) none
      none (.next ([-2272500000000, -9000000000000], [4545000000000, 18000000000000]) none none
      (.next ([-3352500000000, 9000000000000], [6382500000000, -9000000000000]) (some (3, 3, 0))
      (some (3, 3, 0)) (.next ([-5625000000000], [8655000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-7897500000000, -9000000000000], [8655000000000, 0]) (some (3, 1, 0)) (some (3, 1,
      0)) (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded8_2 : ExcludedOn (model8.B 2 ++ [step8.q]) 9000000000000 (model8.caps 2) (model8.ord
    2) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded8_3 : ExcludedOn (model8.B 3 ++ [step8.q]) 9000000000000 (model8.caps 3) (model8.ord
    3) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded8_4 : ExcludedOn (model8.B 4 ++ [step8.q]) 9000000000000 (model8.caps 4) (model8.ord
    4) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded8_5 : ExcludedOn (model8.B 5 ++ [step8.q]) 9000000000000 (model8.caps 5) (model8.ord
    5) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8242500000000, 9000000000000], [1102500000000,
      -9000000000000]) (some (3, 0, 3)) (some (3, 1, 3)) (.next ([5970000000000], [3375000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([3697500000000, -9000000000000], [3375000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2272500000000, 9000000000000], [2272500000000,
      9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0], [2272500000000,
      9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1102500000000, 9000000000000],
      [9345000000000, 0]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-3375000000000],
      [9345000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3375000000000, 0],
      [7072500000000, -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2272500000000,
      -9000000000000], [4545000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 3, 3)) (.terminal
      (some (0, 3, 3)) (some (0, 3, 3)) (some (0, 3, 3))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded8_6 : ExcludedOn (model8.B 6 ++ [step8.q]) 9000000000000 (model8.caps 6) (model8.ord
    6) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2617500000000, 9000000000000], [757500000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([3030000000000], [3352500000000,
      -9000000000000]) (some (2, 0, 2)) (some (2, 0, 2)) (.next ([2272500000000, 9000000000000],
      [6727500000000, -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([345000000000],
      [3030000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [2272500000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-757500000000, 9000000000000],
      [3375000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-3352500000000, 9000000000000],
      [6382500000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6727500000000,
      9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-3030000000000], [3375000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded8_7 : ExcludedOn (model8.B 7 ++ [step8.q]) 9000000000000 (model8.caps 7) (model8.ord
    7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded8_8 : ExcludedOn (model8.B 8 ++ [step8.q]) 9000000000000 (model8.caps 8) (model8.ord
    8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded8_9 : ExcludedOn (model8.B 9 ++ [step8.q]) 9000000000000 (model8.caps 9) (model8.ord
    9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked8 : StepValid model8 9000000000000 step8 0 1 400 := by
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

theorem excluded9_1 : ExcludedOn (model9.B 1 ++ [step9.q]) 9000000000000 (model9.caps 1) (model9.ord
    1) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2992500000000], [2977500000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([2272500000000, 9000000000000], [2272500000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([2992500000000], [5250000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([720000000000, -9000000000000], [7522500000000,
      9000000000000]) (some (0, 3, 2)) none (.next ([0, 0], [2272500000000, 9000000000000]) none
      none (.next ([-2977500000000, 9000000000000], [5970000000000, -9000000000000]) none none
      (.next ([-2272500000000, -9000000000000], [4545000000000, 18000000000000]) (some (3, 1, 0))
      (some (3, 1, 0)) (.next ([-5250000000000], [8242500000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-7522500000000, -9000000000000], [8242500000000, 0]) (some (3, 1, 0)) (some (3, 1,
      0)) (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded9_2 : ExcludedOn (model9.B 2 ++ [step9.q]) 9000000000000 (model9.caps 2) (model9.ord
    2) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded9_3 : ExcludedOn (model9.B 3 ++ [step9.q]) 9000000000000 (model9.caps 3) (model9.ord
    3) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded9_4 : ExcludedOn (model9.B 4 ++ [step9.q]) 9000000000000 (model9.caps 4) (model9.ord
    4) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded9_5 : ExcludedOn (model9.B 5 ++ [step9.q]) 9000000000000 (model9.caps 5) (model9.ord
    5) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded9_6 : ExcludedOn (model9.B 6 ++ [step9.q]) 9000000000000 (model9.caps 6) (model9.ord
    6) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3030000000000, 9000000000000], [720000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([2992500000000], [2977500000000,
      -9000000000000]) (some (2, 0, 2)) (some (2, 0, 2)) (.next ([2272500000000, 9000000000000],
      [6727500000000, -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([757500000000],
      [2992500000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [2272500000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-720000000000, 9000000000000],
      [3750000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-2977500000000, 9000000000000],
      [5970000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6727500000000,
      9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2992500000000], [3750000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded9_7 : ExcludedOn (model9.B 7 ++ [step9.q]) 9000000000000 (model9.caps 7) (model9.ord
    7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded9_8 : ExcludedOn (model9.B 8 ++ [step9.q]) 9000000000000 (model9.caps 8) (model9.ord
    8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded9_9 : ExcludedOn (model9.B 9 ++ [step9.q]) 9000000000000 (model9.caps 9) (model9.ord
    9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked9 : StepValid model9 9000000000000 step9 0 1 400 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded9_1
    · exact excluded9_2
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
    (model10.ord 0) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded10_1 : ExcludedOn (model10.B 1 ++ [step10.q]) 9000000000000 (model10.caps 1)
    (model10.ord 1) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded10_2 : ExcludedOn (model10.B 2 ++ [step10.q]) 9000000000000 (model10.caps 2)
    (model10.ord 2) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded10_3 : ExcludedOn (model10.B 3 ++ [step10.q]) 9000000000000 (model10.caps 3)
    (model10.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded10_4 : ExcludedOn (model10.B 4 ++ [step10.q]) 9000000000000 (model10.caps 4)
    (model10.ord 4) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded10_5 : ExcludedOn (model10.B 5 ++ [step10.q]) 9000000000000 (model10.caps 5)
    (model10.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded10_6 : ExcludedOn (model10.B 6 ++ [step10.q]) 9000000000000 (model10.caps 6)
    (model10.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1515000000000, 0], [7500000000, 9000000000000])
      (some (2, 0, 1)) (some (2, 0, 2)) (.next ([750000000000], [1515000000000]) (some (2, 0, 2))
      (some (2, 3, 2)) (.next ([2272500000000, 9000000000000], [6727500000000, -9000000000000])
      (some (2, 3, 2)) (some (2, 3, 2)) (.next ([750000000000], [8242500000000, -9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [2272500000000, 9000000000000]) (some (0, 3,
      2)) (some (0, 3, 2)) (.next ([-7500000000, -9000000000000], [1522500000000, 9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-1515000000000], [2265000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-6727500000000, 9000000000000], [9000000000000, 0]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-8242500000000, 9000000000000], [8992500000000, -9000000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1, 2)) (some (0, 1,
      2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 400
      (by decide +kernel)
  decide +kernel

theorem excluded10_7 : ExcludedOn (model10.B 7 ++ [step10.q]) 9000000000000 (model10.caps 7)
    (model10.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded10_8 : ExcludedOn (model10.B 8 ++ [step10.q]) 9000000000000 (model10.caps 8)
    (model10.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked10 : StepValid model10 9000000000000 step10 0 1 400 := by
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
    · exact excluded10_8
    · exact (hj rfl).elim
theorem next10 : model10.insert step10 = model11 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded11_0 : ExcludedOn (model11.B 0 ++ [step11.q]) 9000000000000 (model11.caps 0)
    (model11.ord 0) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded11_1 : ExcludedOn (model11.B 1 ++ [step11.q]) 9000000000000 (model11.caps 1)
    (model11.ord 1) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded11_2 : ExcludedOn (model11.B 2 ++ [step11.q]) 9000000000000 (model11.caps 2)
    (model11.ord 2) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded11_3 : ExcludedOn (model11.B 3 ++ [step11.q]) 9000000000000 (model11.caps 3)
    (model11.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded11_4 : ExcludedOn (model11.B 4 ++ [step11.q]) 9000000000000 (model11.caps 4)
    (model11.ord 4) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded11_5 : ExcludedOn (model11.B 5 ++ [step11.q]) 9000000000000 (model11.caps 5)
    (model11.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded11_6 : ExcludedOn (model11.B 6 ++ [step11.q]) 9000000000000 (model11.caps 6)
    (model11.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1465500000000, 0], [807000000000,
      9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([2272500000000, 9000000000000],
      [6727500000000, -9000000000000]) (some (2, 0, 2)) (some (2, 3, 2)) (.next ([0, 0],
      [2272500000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-807000000000,
      -9000000000000], [2272500000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next
      ([-6727500000000, 9000000000000], [9000000000000, 0]) (some (0, 3, 2)) (some (0, 3, 2))
      (.terminal (some (0, 3, 2)) (some (0, 1, 2)) (some (0, 3, 2))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded11_7 : ExcludedOn (model11.B 7 ++ [step11.q]) 9000000000000 (model11.caps 7)
    (model11.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded11_8 : ExcludedOn (model11.B 8 ++ [step11.q]) 9000000000000 (model11.caps 8)
    (model11.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked11 : StepValid model11 9000000000000 step11 0 1 400 := by
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
    · exact excluded11_8
    · exact (hj rfl).elim
theorem next11 : model11.insert step11 = model12 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded12_0 : ExcludedOn (model12.B 0 ++ [step12.q]) 9000000000000 (model12.caps 0)
    (model12.ord 0) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8040000000000], [345000000000]) (some (10, 1,
      4)) (some (10, 2, 4)) (.next ([6386250000000], [382500000000]) (some (10, 2, 4)) (some (10, 2,
      4)) (.next ([7665000000000], [757500000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next
      ([6386250000000], [720000000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next ([6000000000000],
      [1106250000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next ([6011250000000], [1132500000000])
      (some (10, 2, 4)) (some (10, 2, 4)) (.next ([1511250000000], [386250000000]) (some (10, 2, 4))
      (some (10, 2, 4)) (.next ([5625000000000], [1518750000000]) (some (10, 2, 4)) (some (10, 2,
      4)) (.next ([5250000000000], [1481250000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next
      ([1278750000000], [375000000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next ([4863750000000],
      [1481250000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next ([4875000000000], [1893750000000])
      (some (10, 2, 4)) (some (10, 3, 4)) (.next ([4488750000000], [1893750000000]) (some (10, 3,
      4)) (some (10, 3, 4)) (.next ([1522500000000], [750000000000]) (some (10, 3, 4)) (some (10, 3,
      4)) (.next ([2040000000000], [1136250000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next
      ([1278750000000], [761250000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([1653750000000],
      [1136250000000]) (some (10, 3, 4)) (some (10, 3, 4)) fan12Owner0Part1)))))))))))))))))) (den
      := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded12_1 : ExcludedOn (model12.B 1 ++ [step12.q]) 9000000000000 (model12.caps 1)
    (model12.ord 1) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded12_2 : ExcludedOn (model12.B 2 ++ [step12.q]) 9000000000000 (model12.caps 2)
    (model12.ord 2) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4687500000000, 9000000000000], [4312500000000,
      -9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2272500000000, 9000000000000],
      [2272500000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2415000000000],
      [6585000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([142500000000, -9000000000000],
      [6585000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0, 0], [2272500000000,
      9000000000000]) (some (0, 3, 1)) (some (3, 3, 1)) (.next ([-4312500000000, 9000000000000],
      [9000000000000, 0]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([-2272500000000,
      -9000000000000], [4545000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-6585000000000], [9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-6585000000000,
      0], [6727500000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded12_4 : ExcludedOn (model12.B 4 ++ [step12.q]) 9000000000000 (model12.caps 4)
    (model12.ord 4) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6585000000000], [142500000000, -9000000000000])
      (some (3, 0, 3)) (some (3, 1, 3)) (.next ([6585000000000], [2415000000000]) (some (2, 1, 3))
      (some (2, 1, 3)) (.next ([2272500000000, 9000000000000], [2272500000000, 9000000000000]) (some
      (2, 1, 3)) (some (2, 1, 3)) (.next ([4312500000000, -9000000000000], [4687500000000,
      9000000000000]) (some (2, 1, 3)) (some (2, 1, 3)) (.next ([0, 0], [2272500000000,
      9000000000000]) (some (2, 1, 3)) (some (2, 1, 3)) (.next ([-142500000000, 9000000000000],
      [6727500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2415000000000],
      [9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2272500000000, -9000000000000],
      [4545000000000, 18000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-4687500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1,
      3)) (some (0, 3, 3)) (some (0, 3, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded12_5 : ExcludedOn (model12.B 5 ++ [step12.q]) 9000000000000 (model12.caps 5)
    (model12.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded12_6 : ExcludedOn (model12.B 6 ++ [step12.q]) 9000000000000 (model12.caps 6)
    (model12.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded12_7 : ExcludedOn (model12.B 7 ++ [step12.q]) 9000000000000 (model12.caps 7)
    (model12.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded12_8 : ExcludedOn (model12.B 8 ++ [step12.q]) 9000000000000 (model12.caps 8)
    (model12.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded12_9 : ExcludedOn (model12.B 9 ++ [step12.q]) 9000000000000 (model12.caps 9)
    (model12.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked12 : StepValid model12 9000000000000 step12 0 1 400 := by
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
    (model13.ord 0) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6386250000000], [382500000000]) (some (7, 10,
      4)) (some (8, 10, 4)) (.next ([6386250000000], [720000000000]) (some (8, 10, 4)) (some (8, 10,
      4)) (.next ([6000000000000], [1106250000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([6011250000000], [1132500000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([1511250000000], [386250000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([5625000000000],
      [1518750000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([5250000000000], [1481250000000])
      (some (8, 10, 4)) (some (8, 10, 4)) (.next ([4863750000000], [1481250000000]) (some (8, 10,
      4)) (some (8, 10, 4)) (.next ([4875000000000], [1893750000000]) (some (8, 10, 4)) (some (8,
      10, 4)) (.next ([4488750000000], [1893750000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([1522500000000], [750000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([4851750000000],
      [4148250000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([4851750000000], [4534500000000])
      (some (8, 10, 4)) (some (8, 10, 4)) (.next ([375000000000], [375000000000]) (some (8, 10, 4))
      (some (8, 10, 4)) (.next ([4476750000000], [5284500000000]) (some (8, 10, 4)) (some (9, 10,
      4)) (.next ([4090500000000], [5670750000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next
      ([3340500000000], [6045750000000]) (some (9, 10, 4)) (some (9, 10, 4))
      fan13Owner0Part1)))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded13_1 : ExcludedOn (model13.B 1 ++ [step13.q]) 9000000000000 (model13.caps 1)
    (model13.ord 1) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded13_2 : ExcludedOn (model13.B 2 ++ [step13.q]) 9000000000000 (model13.caps 2)
    (model13.ord 2) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded13_3 : ExcludedOn (model13.B 3 ++ [step13.q]) 9000000000000 (model13.caps 3)
    (model13.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded13_4 : ExcludedOn (model13.B 4 ++ [step13.q]) 9000000000000 (model13.caps 4)
    (model13.ord 4) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded13_6 : ExcludedOn (model13.B 6 ++ [step13.q]) 9000000000000 (model13.caps 6)
    (model13.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded13_7 : ExcludedOn (model13.B 7 ++ [step13.q]) 9000000000000 (model13.caps 7)
    (model13.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded13_8 : ExcludedOn (model13.B 8 ++ [step13.q]) 9000000000000 (model13.caps 8)
    (model13.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded13_9 : ExcludedOn (model13.B 9 ++ [step13.q]) 9000000000000 (model13.caps 9)
    (model13.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([750000000000], [49500000000]) (some (4, 0, 1))
      (some (4, 1, 2)) (.next ([6735000000000], [750000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([5284500000000, 0], [1818000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([1890000000000], [1450500000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([5284500000000], [4090500000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1840500000000],
      [2250000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2272500000000, 9000000000000],
      [5262000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1522500000000,
      9000000000000], [5212500000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0,
      0], [2272500000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-49500000000],
      [799500000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-750000000000], [7485000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-1818000000000, 9000000000000], [7102500000000,
      -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-1450500000000], [3340500000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4090500000000], [9375000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-2250000000000], [4090500000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-5262000000000, 9000000000000], [7534500000000, 0]) (some (0, 1, 2)) (some (0, 1, 4))
      (.next ([-5212500000000, 9000000000000], [6735000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4))
      (.terminal (some (0, 1, 4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem checked13 : StepValid model13 9000000000000 step13 0 1 400 := by
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
    · exact excluded13_4
    · exact (hj rfl).elim
    · exact excluded13_6
    · exact excluded13_7
    · exact excluded13_8
    · exact excluded13_9
theorem next13 : model13.insert step13 = model14 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded14_0 : ExcludedOn (model14.B 0 ++ [step14.q]) 9000000000000 (model14.caps 0)
    (model14.ord 0) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6386250000000], [382500000000]) (some (7, 10,
      4)) (some (8, 10, 4)) (.next ([6386250000000], [720000000000]) (some (8, 10, 4)) (some (8, 10,
      4)) (.next ([6000000000000], [1106250000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([6011250000000], [1132500000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([1511250000000], [386250000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([5625000000000],
      [1518750000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([5250000000000], [1481250000000])
      (some (8, 10, 4)) (some (8, 10, 4)) (.next ([4863750000000], [1481250000000]) (some (8, 10,
      4)) (some (8, 10, 4)) (.next ([4875000000000], [1893750000000]) (some (8, 10, 4)) (some (8,
      10, 4)) (.next ([4488750000000], [1893750000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([1522500000000], [750000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([4691250000000],
      [4683750000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([375000000000], [375000000000])
      (some (8, 10, 4)) (some (8, 10, 4)) (.next ([4691250000000], [5070000000000]) (some (8, 10,
      4)) (some (9, 10, 4)) (.next ([4316250000000], [5820000000000]) (some (9, 10, 4)) (some (9,
      10, 4)) (.next ([3930000000000], [6206250000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next
      ([375000000000], [761250000000]) (some (9, 10, 4)) (some (9, 10, 4))
      fan14Owner0Part1)))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded14_1 : ExcludedOn (model14.B 1 ++ [step14.q]) 9000000000000 (model14.caps 1)
    (model14.ord 1) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded14_2 : ExcludedOn (model14.B 2 ++ [step14.q]) 9000000000000 (model14.caps 2)
    (model14.ord 2) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded14_3 : ExcludedOn (model14.B 3 ++ [step14.q]) 9000000000000 (model14.caps 3)
    (model14.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded14_4 : ExcludedOn (model14.B 4 ++ [step14.q]) 9000000000000 (model14.caps 4)
    (model14.ord 4) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded14_6 : ExcludedOn (model14.B 6 ++ [step14.q]) 9000000000000 (model14.caps 6)
    (model14.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded14_7 : ExcludedOn (model14.B 7 ++ [step14.q]) 9000000000000 (model14.caps 7)
    (model14.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded14_8 : ExcludedOn (model14.B 8 ++ [step14.q]) 9000000000000 (model14.caps 8)
    (model14.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded14_9 : ExcludedOn (model14.B 9 ++ [step14.q]) 9000000000000 (model14.caps 9)
    (model14.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([750000000000], [49500000000]) (some (4, 0, 1))
      (some (4, 1, 2)) (.next ([6735000000000], [750000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([5445000000000, 0], [1282500000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([5445000000000], [3555000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([1515000000000], [1290000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1465500000000],
      [2089500000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2272500000000, 9000000000000],
      [5262000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1522500000000,
      9000000000000], [5212500000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0,
      0], [2272500000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-49500000000],
      [799500000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-750000000000], [7485000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-1282500000000, 9000000000000], [6727500000000,
      -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-3555000000000], [9000000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1290000000000], [2805000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-2089500000000], [3555000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-5262000000000, 9000000000000], [7534500000000, 0]) (some (0, 1, 2)) (some (0, 1, 4))
      (.next ([-5212500000000, 9000000000000], [6735000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4))
      (.terminal (some (0, 1, 4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem checked14 : StepValid model14 9000000000000 step14 0 1 400 := by
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
    (model15.ord 0) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded15_1 : ExcludedOn (model15.B 1 ++ [step15.q]) 9000000000000 (model15.caps 1)
    (model15.ord 1) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded15_2 : ExcludedOn (model15.B 2 ++ [step15.q]) 9000000000000 (model15.caps 2)
    (model15.ord 2) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded15_3 : ExcludedOn (model15.B 3 ++ [step15.q]) 9000000000000 (model15.caps 3)
    (model15.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded15_4 : ExcludedOn (model15.B 4 ++ [step15.q]) 9000000000000 (model15.caps 4)
    (model15.ord 4) 0 1 400 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded15_5 : ExcludedOn (model15.B 5 ++ [step15.q]) 9000000000000 (model15.caps 5)
    (model15.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded15_6 : ExcludedOn (model15.B 6 ++ [step15.q]) 9000000000000 (model15.caps 6)
    (model15.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded15_7 : ExcludedOn (model15.B 7 ++ [step15.q]) 9000000000000 (model15.caps 7)
    (model15.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded15_9 : ExcludedOn (model15.B 9 ++ [step15.q]) 9000000000000 (model15.caps 9)
    (model15.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked15 : StepValid model15 9000000000000 step15 0 1 400 := by
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

end Sext252500255000
end ConwaySoifer.Simplified.Certificates
