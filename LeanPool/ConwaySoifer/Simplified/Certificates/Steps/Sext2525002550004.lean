/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext252500255000
import Mathlib.Tactic.FinCases

/-!
# Sext 252500 255000 4

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
def fan32Owner0Part0 : FanWitness := (.next ([-2002500000000], [7627500000000]) (some (0, 1, 7))
    (some (0, 1, 7)) (.next ([-761250000000], [2793750000000]) (some (0, 1, 7)) (some (0, 1, 7))
    (.next ([-2415000000000], [7665000000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next
    ([-375000000000], [1136250000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-1136250000000],
    [2418750000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-375000000000], [750000000000])
    (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-3693750000000], [6750000000000]) (some (0, 1, 7))
    (some (0, 1, 7)) (.next ([-3318750000000], [6000000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-3318750000000], [5613750000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-4455000000000], [7515000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1136250000000],
    [1901250000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1140000000000], [1657500000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1136250000000], [1515000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-6112500000000], [8032500000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-5208750000000], [6000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-5595000000000], [6386250000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3330000000000],
    [3697500000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3705000000000], [4110000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-375000000000], [412500000000]) (some (0, 1, 5))
    (some (0, 7, 5)) (.next ([-5246250000000], [5625000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-5632500000000], [6011250000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-6345000000000], [6761250000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-761250000000],
    [765000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-6382500000000], [6386250000000])
    (some (0, 7, 5)) (some (0, 7, 6)) (.terminal (some (0, 7, 6)) (some (0, 7, 6)) (some (0, 7,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner0Part1 : FanWitness := (.next ([1282500000000], [1136250000000]) (some (6, 1, 7))
    (some (6, 1, 7)) (.next ([375000000000], [375000000000]) (some (6, 1, 7)) (some (6, 1, 7))
    (.next ([3056250000000], [3693750000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
    ([2681250000000], [3318750000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([2295000000000],
    [3318750000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([3060000000000], [4455000000000])
    (some (6, 1, 7)) (some (6, 1, 7)) (.next ([765000000000], [1136250000000]) (some (6, 1, 7))
    (some (6, 1, 7)) (.next ([517500000000], [1140000000000]) (some (6, 1, 7)) (some (6, 1, 7))
    (.next ([378750000000], [1136250000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next
    ([1920000000000], [6112500000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next ([791250000000],
    [5208750000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next ([791250000000], [5595000000000])
    (some (0, 1, 7)) (some (0, 1, 7)) (.next ([367500000000], [3330000000000]) (some (0, 1, 7))
    (some (0, 1, 7)) (.next ([405000000000], [3705000000000]) (some (0, 1, 7)) (some (0, 1, 7))
    (.next ([37500000000], [375000000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next ([378750000000],
    [5246250000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next ([378750000000], [5632500000000])
    (some (0, 1, 7)) (some (0, 1, 7)) (.next ([416250000000], [6345000000000]) (some (0, 1, 7))
    (some (0, 1, 7)) (.next ([3750000000], [761250000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next
    ([3750000000], [6382500000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next ([0], [386250000000])
    (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-345000000000], [7110000000000]) (some (0, 1, 7))
    (some (0, 1, 7)) (.next ([-757500000000], [7147500000000]) (some (0, 1, 7)) (some (0, 1, 7))
    (.next ([-375000000000], [2793750000000]) (some (0, 1, 7)) (some (0, 1, 7))
    fan32Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner4Part0 : FanWitness := (.next ([1488750000000], [363750000000]) (some (4, 1, 5)) (some
    (4, 1, 5)) (.next ([4875000000000], [1852500000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([3772500000000], [1818000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([4125000000000],
    [2272500000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([4545000000000], [2602500000000])
    (some (4, 1, 2)) (some (4, 1, 2)) (.next ([772500000000], [784500000000]) (some (4, 1, 2)) (some
    (4, 1, 2)) (.next ([1557000000000, 9000000000000], [3352500000000, -9000000000000]) (some (4, 1,
    2)) (some (4, 1, 3)) (.next ([2272500000000, 9000000000000], [5238750000000]) (some (4, 1, 3))
    (some (4, 1, 3)) (.next ([420000000000, 9000000000000], [6727500000000]) (some (4, 1, 3)) (some
    (4, 1, 3)) (.next ([0, 9000000000000], [4125000000000, -9000000000000]) (some (4, 1, 3)) (some
    (4, 1, 3)) (.next ([0], [5238750000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
    ([-329250000000], [5954250000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-715500000000],
    [5625000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1113750000000], [7511250000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-363750000000], [1852500000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([-1852500000000], [6727500000000]) (some (0, 1, 3)) (some (0, 5, 3))
    (.next ([-1818000000000], [5590500000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-2272500000000], [6397500000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2602500000000],
    [7147500000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-784500000000], [1557000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3352500000000, 9000000000000], [4909500000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-5238750000000], [7511250000000, 9000000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-6727500000000], [7147500000000, 9000000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4125000000000, 9000000000000], [4125000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3)) (some (0, 5, 4)) (some (0, 5,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner3Part0 : FanWitness := (.next ([2040000000000], [4545000000000]) (some (5, 6, 3))
    (some (5, 6, 3)) (.next ([1702500000000], [4125000000000]) (some (5, 6, 3)) (some (5, 6, 3))
    (.next ([1515000000000, 9000000000000], [4882500000000]) (some (5, 6, 3)) (some (5, 6, 3))
    (.next ([1372500000000], [6727500000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
    ([90000000000, 9000000000000], [2160000000000, -9000000000000]) (some (5, 6, 3)) (some (5, 6,
    3)) (.next ([0], [4545000000000]) (some (5, 6, 3)) (some (5, 6, 4)) (.next ([-142500000000],
    [1515000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-757500000000], [4882500000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2295000000000], [6727500000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-2295000000000], [5850000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-2632500000000], [6307500000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-2752500000000], [5970000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3172500000000],
    [6727500000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2182500000000], [4432500000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2152500000000], [4335000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-4455000000000, 9000000000000], [8100000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-420000000000], [757500000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-4312500000000, 9000000000000], [6585000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-4545000000000, 0], [6817500000000, 9000000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-4545000000000], [6585000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-4125000000000], [5827500000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-4882500000000,
    0], [6397500000000, 9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-6727500000000],
    [8100000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2160000000000, 9000000000000],
    [2250000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.terminal (some (0, 6, 4)) (some (0, 6, 4))
    (some (0, 6, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner4Part0 : FanWitness := (.next ([4909500000000], [715500000000]) (some (4, 1, 5)) (some
    (4, 1, 5)) (.next ([6397500000000], [1113750000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([4125000000000], [2272500000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1372500000000],
    [1230000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([772500000000], [784500000000]) (some
    (4, 1, 5)) (some (4, 1, 5)) (.next ([1557000000000, 9000000000000], [3352500000000,
    -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2272500000000, 9000000000000],
    [5238750000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1372500000000, 9000000000000],
    [5355000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1488750000000],
    [6138750000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0, 9000000000000], [4125000000000,
    -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0], [5238750000000]) (some (4, 1,
    5)) (some (4, 1, 5)) (.next ([-329250000000], [5954250000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-184500000000], [2002500000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-900000000000], [7627500000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-715500000000],
    [5625000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1113750000000], [7511250000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2272500000000], [6397500000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-1230000000000], [2602500000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-784500000000], [1557000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-3352500000000, 9000000000000], [4909500000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-5238750000000], [7511250000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-5355000000000, 9000000000000], [6727500000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-6138750000000], [7627500000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-4125000000000,
    9000000000000], [4125000000000]) (some (0, 1, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3))
    (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan36Owner2Part0 : FanWitness := (.next ([2575500000000], [1534500000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([5212500000000, -9000000000000], [3397500000000, 9000000000000]) (some
    (0, 5, 3)) (some (0, 5, 3)) (.next ([3787500000000, 9000000000000], [2602500000000,
    -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2637000000000, -9000000000000],
    [1863000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2682000000000,
    9000000000000], [2227500000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([2272500000000, 9000000000000], [2272500000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([1095000000000], [2640000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([1515000000000], [4875000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([1147500000000,
    9000000000000], [6337500000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([409500000000], [4500000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0, 0],
    [2272500000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1125000000000],
    [8610000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next ([-757500000000, -9000000000000],
    [4875000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-375000000000], [1480500000000])
    (some (0, 5, 4)) (some (1, 5, 4)) (.next ([-1534500000000], [4110000000000]) (some (1, 5, 4))
    (some (1, 5, 4)) (.next ([-3397500000000, -9000000000000], [8610000000000]) (some (1, 5, 4))
    (some (1, 5, 4)) (.next ([-2602500000000, 9000000000000], [6390000000000, 0]) (some (1, 5, 4))
    (some (1, 5, 4)) (.next ([-1863000000000, -9000000000000], [4500000000000]) (some (1, 5, 4))
    (some (1, 5, 4)) (.next ([-2227500000000, 9000000000000], [4909500000000, 0]) (some (1, 5, 4))
    (some (1, 5, 4)) (.next ([-2272500000000, -9000000000000], [4545000000000, 18000000000000])
    (some (1, 5, 4)) (some (1, 5, 4)) (.next ([-2640000000000], [3735000000000]) (some (1, 5, 4))
    (some (1, 5, 4)) (.next ([-4875000000000], [6390000000000]) (some (1, 5, 4)) (some (5, 5, 4))
    (.next ([-6337500000000, 9000000000000], [7485000000000, 0]) (some (5, 5, 4)) (some (5, 5, 4))
    (.next ([-4500000000000], [4909500000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.terminal (some
    (5, 3, 4)) (some (5, 3, 0)) (some (5, 3, 4)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6765000000000], [345000000000]) (some (6, 0, 7))
      (some (6, 0, 7)) (.next ([6390000000000], [757500000000]) (some (6, 0, 7)) (some (6, 0, 7))
      (.next ([2418750000000], [375000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next
      ([5625000000000], [2002500000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next ([2032500000000],
      [761250000000]) (some (6, 0, 7)) (some (6, 1, 7)) (.next ([5250000000000], [2415000000000])
      (some (6, 1, 7)) (some (6, 1, 7)) (.next ([761250000000], [375000000000]) (some (6, 1, 7))
      (some (6, 1, 7)) fan32Owner0Part1))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded32_2 : ExcludedOn (model32.B 2 ++ [step32.q]) 9000000000000 (model32.caps 2)
    (model32.ord 2) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded32_3 : ExcludedOn (model32.B 3 ++ [step32.q]) 9000000000000 (model32.caps 3)
    (model32.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded32_4 : ExcludedOn (model32.B 4 ++ [step32.q]) 9000000000000 (model32.caps 4)
    (model32.ord 4) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded32_5 : ExcludedOn (model32.B 5 ++ [step32.q]) 9000000000000 (model32.caps 5)
    (model32.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded32_6 : ExcludedOn (model32.B 6 ++ [step32.q]) 9000000000000 (model32.caps 6)
    (model32.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6727500000000, 9000000000000], [352500000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([4455000000000], [2625000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2272500000000, 9000000000000], [6727500000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([352500000000, 9000000000000],
      [2272500000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [2272500000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-352500000000,
      9000000000000], [7080000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-2625000000000],
      [7080000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6727500000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2272500000000, 9000000000000],
      [2625000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded32_7 : ExcludedOn (model32.B 7 ++ [step32.q]) 9000000000000 (model32.caps 7)
    (model32.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded32_8 : ExcludedOn (model32.B 8 ++ [step32.q]) 9000000000000 (model32.caps 8)
    (model32.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded32_9 : ExcludedOn (model32.B 9 ++ [step32.q]) 9000000000000 (model32.caps 9)
    (model32.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked32 : StepValid model32 9000000000000 step32 0 1 400 := by
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

theorem excluded33_0 : ExcludedOn (model33.B 0 ++ [step33.q]) 9000000000000 (model33.caps 0)
    (model33.ord 0) 0 1 400 := by
  apply ExclusionHint.sound (.pair 1 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded33_1 : ExcludedOn (model33.B 1 ++ [step33.q]) 9000000000000 (model33.caps 1)
    (model33.ord 1) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded33_2 : ExcludedOn (model33.B 2 ++ [step33.q]) 9000000000000 (model33.caps 2)
    (model33.ord 2) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded33_3 : ExcludedOn (model33.B 3 ++ [step33.q]) 9000000000000 (model33.caps 3)
    (model33.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.pair 3 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded33_5 : ExcludedOn (model33.B 5 ++ [step33.q]) 9000000000000 (model33.caps 5)
    (model33.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6363000000000, 9000000000000], [387000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([4090500000000], [2659500000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1305000000000], [1354500000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([3761250000000], [5445000000000]) (some (4, 1, 2)) (some (4, 1, 3))
      (.next ([2272500000000, 9000000000000], [5445000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([1101750000000], [6750000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0, 0],
      [2272500000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-387000000000,
      9000000000000], [6750000000000, 0]) (some (4, 1, 3)) (some (4, 2, 3)) (.next
      ([-2659500000000], [6750000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-1354500000000], [2659500000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-5445000000000], [9206250000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-5445000000000,
      0], [7717500000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-6750000000000], [7851750000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some (4, 2,
      3)) (some (0, 2, 4)) (some (4, 2, 4))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded33_7 : ExcludedOn (model33.B 7 ++ [step33.q]) 9000000000000 (model33.caps 7)
    (model33.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded33_8 : ExcludedOn (model33.B 8 ++ [step33.q]) 9000000000000 (model33.caps 8)
    (model33.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded33_9 : ExcludedOn (model33.B 9 ++ [step33.q]) 9000000000000 (model33.caps 9)
    (model33.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked33 : StepValid model33 9000000000000 step33 0 1 400 := by
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
    · exact (hj rfl).elim
    · exact excluded33_5
    · exact excluded33_6
    · exact excluded33_7
    · exact excluded33_8
    · exact excluded33_9
theorem next33 : model33.insert step33 = model34 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded34_1 : ExcludedOn (model34.B 1 ++ [step34.q]) 9000000000000 (model34.caps 1)
    (model34.ord 1) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded34_3 : ExcludedOn (model34.B 3 ++ [step34.q]) 9000000000000 (model34.caps 3)
    (model34.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.pair 3 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded34_4 : ExcludedOn (model34.B 4 ++ [step34.q]) 9000000000000 (model34.caps 4)
    (model34.ord 4) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5625000000000], [329250000000]) (some (4, 0, 5))
      (some (4, 1, 5)) (.next ([4909500000000], [715500000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([6397500000000], [1113750000000]) (some (4, 1, 5)) (some (4, 1, 5))
      fan34Owner4Part0)))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6363000000000, 9000000000000], [387000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([4090500000000], [2659500000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([4125000000000], [3592500000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([1305000000000], [1354500000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([1852500000000], [2272500000000]) (some (4, 1, 2)) (some (4, 1, 3)) (.next
      ([2272500000000, 9000000000000], [5445000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([1465500000000], [4897500000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0,
      9000000000000], [1852500000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0,
      0], [2272500000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-387000000000,
      9000000000000], [6750000000000, 0]) (some (0, 1, 3)) (some (0, 2, 3)) (.next
      ([-2659500000000], [6750000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-3592500000000], [7717500000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-1354500000000], [2659500000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-2272500000000], [4125000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-5445000000000,
      0], [7717500000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-4897500000000], [6363000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1852500000000,
      9000000000000], [1852500000000, 0]) (some (0, 2, 3)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded34_7 : ExcludedOn (model34.B 7 ++ [step34.q]) 9000000000000 (model34.caps 7)
    (model34.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded34_8 : ExcludedOn (model34.B 8 ++ [step34.q]) 9000000000000 (model34.caps 8)
    (model34.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded34_9 : ExcludedOn (model34.B 9 ++ [step34.q]) 9000000000000 (model34.caps 9)
    (model34.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked34 : StepValid model34 9000000000000 step34 0 1 400 := by
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

theorem excluded35_1 : ExcludedOn (model35.B 1 ++ [step35.q]) 9000000000000 (model35.caps 1)
    (model35.ord 1) 0 1 400 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded35_2 : ExcludedOn (model35.B 2 ++ [step35.q]) 9000000000000 (model35.caps 2)
    (model35.ord 2) 0 1 400 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded35_3 : ExcludedOn (model35.B 3 ++ [step35.q]) 9000000000000 (model35.caps 3)
    (model35.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1372500000000], [142500000000]) (some (4, 0, 6))
      (some (5, 0, 6)) (.next ([4125000000000], [757500000000]) (some (5, 0, 2)) (some (5, 0, 2))
      (.next ([4432500000000], [2295000000000]) (some (5, 0, 2)) (some (5, 0, 2)) (.next
      ([3555000000000], [2295000000000]) (some (5, 0, 2)) (some (5, 0, 2)) (.next ([3675000000000],
      [2632500000000]) (some (5, 0, 2)) (some (5, 0, 2)) (.next ([3217500000000], [2752500000000])
      (some (5, 0, 2)) (some (5, 0, 2)) (.next ([3555000000000], [3172500000000]) (some (5, 0, 2))
      (some (5, 0, 2)) (.next ([2250000000000], [2182500000000]) (some (5, 0, 2)) (some (5, 6, 2))
      (.next ([2182500000000], [2152500000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
      ([3645000000000, 9000000000000], [4455000000000, -9000000000000]) (some (5, 6, 2)) (some (5,
      6, 3)) (.next ([337500000000], [420000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([2272500000000, 9000000000000], [4312500000000, -9000000000000]) (some (5, 6, 3)) (some (5,
      6, 3)) (.next ([2272500000000, 9000000000000], [4545000000000]) (some (5, 6, 3)) (some (5, 6,
      3)) fan35Owner3Part0)))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded35_4 : ExcludedOn (model35.B 4 ++ [step35.q]) 9000000000000 (model35.caps 4)
    (model35.ord 4) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5625000000000], [329250000000]) (some (4, 0, 5))
      (some (4, 1, 5)) (.next ([1818000000000], [184500000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([6727500000000], [900000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      fan35Owner4Part0)))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded35_5 : ExcludedOn (model35.B 5 ++ [step35.q]) 9000000000000 (model35.caps 5)
    (model35.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded35_6 : ExcludedOn (model35.B 6 ++ [step35.q]) 9000000000000 (model35.caps 6)
    (model35.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded35_7 : ExcludedOn (model35.B 7 ++ [step35.q]) 9000000000000 (model35.caps 7)
    (model35.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded35_8 : ExcludedOn (model35.B 8 ++ [step35.q]) 9000000000000 (model35.caps 8)
    (model35.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded35_9 : ExcludedOn (model35.B 9 ++ [step35.q]) 9000000000000 (model35.caps 9)
    (model35.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked35 : StepValid model35 9000000000000 step35 0 1 400 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded35_1
    · exact excluded35_2
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

theorem excluded36_1 : ExcludedOn (model36.B 1 ++ [step36.q]) 9000000000000 (model36.caps 1)
    (model36.ord 1) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5602500000000, -9000000000000], [1882500000000,
      9000000000000]) (some (3, 4, 1)) none (.next ([2625000000000], [1920000000000]) none none
      (.next ([2272500000000, 9000000000000], [2272500000000, 9000000000000]) none none (.next
      ([2310000000000], [2940000000000]) none none (.next ([2662500000000, 9000000000000],
      [5212500000000, -9000000000000]) none none (.next ([352500000000, 9000000000000],
      [2272500000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([352500000000,
      -9000000000000], [4192500000000, 9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next
      ([390000000000], [7485000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0],
      [2272500000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-1882500000000,
      -9000000000000], [7485000000000, 0]) (some (4, 1, 2)) (some (4, 1, 3)) (.next
      ([-1920000000000], [4545000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-2272500000000,
      -9000000000000], [4545000000000, 18000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-2940000000000], [5250000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-5212500000000,
      9000000000000], [7875000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-2272500000000,
      9000000000000], [2625000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-4192500000000,
      -9000000000000], [4545000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-7485000000000], [7875000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1,
      3)) (some (4, 1, 3)) (some (4, 1, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded36_2 : ExcludedOn (model36.B 2 ++ [step36.q]) 9000000000000 (model36.caps 2)
    (model36.ord 2) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7485000000000], [1125000000000]) (some (0, 5,
      3)) (some (0, 5, 3)) (.next ([4117500000000, -9000000000000], [757500000000, 9000000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([1105500000000], [375000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) fan36Owner2Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded36_3 : ExcludedOn (model36.B 3 ++ [step36.q]) 9000000000000 (model36.caps 3)
    (model36.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.pair 5 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded36_4 : ExcludedOn (model36.B 4 ++ [step36.q]) 9000000000000 (model36.caps 4)
    (model36.ord 4) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded36_6 : ExcludedOn (model36.B 6 ++ [step36.q]) 9000000000000 (model36.caps 6)
    (model36.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3787500000000, 9000000000000], [5602500000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([2662500000000, 9000000000000],
      [5212500000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2272500000000,
      9000000000000], [6727500000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([1515000000000], [7875000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [2272500000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-5602500000000,
      9000000000000], [9390000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-5212500000000,
      9000000000000], [7875000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6727500000000,
      9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 3)) (.next
      ([-7875000000000], [9390000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1,
      3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded36_7 : ExcludedOn (model36.B 7 ++ [step36.q]) 9000000000000 (model36.caps 7)
    (model36.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded36_8 : ExcludedOn (model36.B 8 ++ [step36.q]) 9000000000000 (model36.caps 8)
    (model36.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded36_9 : ExcludedOn (model36.B 9 ++ [step36.q]) 9000000000000 (model36.caps 9)
    (model36.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked36 : StepValid model36 9000000000000 step36 0 1 400 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded36_1
    · exact excluded36_2
    · exact excluded36_3
    · exact excluded36_4
    · exact excluded36_5
    · exact excluded36_6
    · exact excluded36_7
    · exact excluded36_8
    · exact excluded36_9
theorem next36 : model36.insert step36 = model37 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext252500255000
end ConwaySoifer.Simplified.Certificates
