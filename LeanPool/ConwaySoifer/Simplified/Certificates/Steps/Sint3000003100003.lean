/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint300000310000
import Mathlib.Tactic.FinCases

/-!
# Sint 300000 310000 3

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
namespace Sint300000310000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner4Part0 : FanWitness := (.next ([825000000000], [4575000000000]) (some (6, 7, 3)) (some
    (6, 7, 4)) (.next ([0, 9000000000000], [750000000000, -9000000000000]) (some (6, 7, 4)) (some
    (6, 7, 4)) (.next ([0], [2850000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
    ([-285000000000], [5235000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([-150000000000],
    [2625000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([-375000000000], [2700000000000])
    (some (0, 7, 4)) (some (0, 7, 4)) (.next ([-1125000000000], [5625000000000]) (some (0, 7, 4))
    (some (0, 7, 4)) (.next ([-1050000000000], [4575000000000]) (some (0, 7, 4)) (some (0, 7, 4))
    (.next ([-1875000000000, 9000000000000], [6375000000000]) (some (0, 7, 4)) (some (0, 7, 4))
    (.next ([-1500000000000], [4200000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
    ([-2100000000000], [5550000000000]) (some (0, 7, 4)) (some (0, 7, 5)) (.next ([-2250000000000,
    9000000000000], [4950000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-900000000000],
    [1950000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-2625000000000], [5325000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-2850000000000], [5550000000000, 9000000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-4485000000000], [7935000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-2850000000000], [4950000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-5235000000000], [7935000000000, 9000000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-4575000000000], [6375000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-3435000000000], [4575000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-2700000000000],
    [3450000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-1425000000000], [1800000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-4575000000000], [5400000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([-750000000000, 9000000000000], [750000000000]) (some (0, 3, 5)) (some
    (0, 3, 5)) (.terminal (some (0, 3, 5)) (some (0, 3, 6)) (some (0, 3,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner3Part0 : FanWitness := (.next ([3735000000000], [540000000000]) (some (4, 0, 5)) (some
    (4, 0, 5)) (.next ([3300000000000], [1350000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
    ([4500000000000], [2400000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([4875000000000],
    [2835000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([4875000000000], [2850000000000])
    (some (4, 0, 5)) (some (4, 0, 5)) (.next ([375000000000], [435000000000]) (some (4, 0, 5)) (some
    (4, 0, 5)) (.next ([375000000000], [450000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
    ([3750000000000], [5400000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([450000000000],
    [4050000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([900000000000], [8250000000000])
    (some (4, 0, 5)) (some (4, 0, 5)) (.next ([15000000000], [4860000000000]) (some (4, 0, 5)) (some
    (4, 5, 5)) (.next ([0], [2850000000000]) (some (4, 5, 5)) (some (4, 5, 5)) (.next
    ([-525000000000], [4275000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-540000000000],
    [4275000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1350000000000], [4650000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2400000000000], [6900000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-2835000000000], [7710000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-2850000000000], [7725000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-435000000000], [810000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-450000000000],
    [825000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-5400000000000], [9150000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4050000000000], [4500000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-8250000000000], [9150000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-4860000000000], [4875000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some
    (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan29Owner5Part0 : FanWitness := (.next ([3900000000000], [4050000000000]) (some (6, 1, 4))
    (some (6, 1, 4)) (.next ([2490000000000], [3000000000000]) (some (6, 1, 4)) (some (6, 1, 4))
    (.next ([2340000000000], [2925000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
    ([2865000000000], [3900000000000]) (some (6, 1, 4)) (some (6, 1, 5)) (.next ([2640000000000],
    [4050000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([300000000000, -9000000000000],
    [900000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([225000000000, -9000000000000],
    [1125000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([0], [3765000000000]) (some (6, 1,
    5)) (some (6, 1, 5)) (.next ([-1365000000000], [6390000000000]) (some (6, 1, 5)) (some (6, 2,
    5)) (.next ([-900000000000], [3900000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next
    ([-1125000000000], [4050000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-75000000000],
    [225000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-2700000000000, -9000000000000],
    [7725000000000, 9000000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-2625000000000],
    [6390000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-2700000000000, -9000000000000],
    [6465000000000, 9000000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-2700000000000,
    -9000000000000], [6390000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-3900000000000],
    [8025000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-4050000000000], [7950000000000])
    (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-3000000000000], [5490000000000]) (some (6, 2, 5))
    (some (6, 2, 5)) (.next ([-2925000000000], [5265000000000]) (some (6, 2, 5)) (some (6, 2, 5))
    (.next ([-3900000000000], [6765000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next
    ([-4050000000000], [6690000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-900000000000,
    0], [1200000000000, -9000000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-1125000000000,
    0], [1350000000000, -9000000000000]) (some (6, 2, 5)) (some (6, 3, 5)) (.terminal (some (6, 3,
    5)) (some (0, 3, 5)) (some (6, 3, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan30Owner5Part0 : FanWitness := (.next ([2640000000000], [4050000000000]) (some (6, 1, 5))
    (some (6, 1, 5)) (.next ([1800000000000], [3600000000000]) (some (6, 1, 5)) (some (6, 1, 5))
    (.next ([300000000000, -9000000000000], [900000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next
    ([225000000000, -9000000000000], [1125000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next
    ([165000000000], [1635000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([0],
    [3765000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-900000000000, -9000000000000],
    [6300000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-990000000000],
    [4590000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-900000000000], [3900000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1125000000000], [4050000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-2100000000000], [6600000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-75000000000], [225000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-2250000000000], [6525000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2625000000000],
    [6390000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2700000000000, -9000000000000],
    [6465000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2700000000000,
    -9000000000000], [6390000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3000000000000],
    [5490000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2925000000000], [5265000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3900000000000], [6765000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-4050000000000], [6690000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-3600000000000], [5400000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-900000000000, 0], [1200000000000, -9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1125000000000, 0], [1350000000000, -9000000000000]) (some (0, 2, 5)) (some (0, 3, 5)) (.next
    ([-1635000000000], [1800000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.terminal (some (0, 3,
    5)) (some (0, 3, 5)) (some (0, 3, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan31Owner5Part0 : FanWitness := (.next ([2490000000000], [3000000000000]) (some (6, 1, 4))
    (some (6, 1, 4)) (.next ([2340000000000], [2925000000000]) (some (6, 1, 4)) (some (6, 1, 4))
    (.next ([2865000000000], [3900000000000]) (some (6, 1, 4)) (some (6, 1, 5)) (.next
    ([2640000000000], [4050000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([615000000000],
    [2085000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([225000000000, -9000000000000],
    [1125000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0], [3765000000000]) (some (0, 1,
    5)) (some (0, 1, 5)) (.next ([0, -9000000000000], [5850000000000, 9000000000000]) (some (0, 1,
    5)) (some (0, 2, 5)) (.next ([-540000000000], [3690000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-1200000000000], [6150000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1350000000000], [6075000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-900000000000],
    [3900000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1125000000000], [4050000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-75000000000], [225000000000]) (some (0, 2, 5)) (some
    (0, 2, 5)) (.next ([-2625000000000], [6390000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-2700000000000, -9000000000000], [6465000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2,
    5)) (.next ([-2700000000000, -9000000000000], [6390000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-3150000000000], [5850000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-3000000000000], [5490000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2925000000000],
    [5265000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3900000000000], [6765000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4050000000000], [6690000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-2085000000000], [2700000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-1125000000000, 0], [1350000000000, -9000000000000]) (some (0, 2, 5)) (some (0, 3, 5))
    (.terminal (some (0, 3, 5)) (some (0, 3, 5)) (some (0, 3, 5)))))))))))))))))))))))))))

theorem excluded24_0 : ExcludedOn (model24.B 0 ++ [step24.q]) 9000000000000 (model24.caps 0)
    (model24.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_1 : ExcludedOn (model24.B 1 ++ [step24.q]) 9000000000000 (model24.caps 1)
    (model24.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_2 : ExcludedOn (model24.B 2 ++ [step24.q]) 9000000000000 (model24.caps 2)
    (model24.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_3 : ExcludedOn (model24.B 3 ++ [step24.q]) 9000000000000 (model24.caps 3)
    (model24.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_4 : ExcludedOn (model24.B 4 ++ [step24.q]) 9000000000000 (model24.caps 4)
    (model24.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4950000000000], [285000000000]) (some (6, 0, 3))
      (some (6, 7, 3)) (.next ([2475000000000], [150000000000]) (some (6, 7, 3)) (some (6, 7, 3))
      (.next ([2325000000000], [375000000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next
      ([4500000000000], [1125000000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next ([3525000000000],
      [1050000000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next ([4500000000000, 9000000000000],
      [1875000000000, -9000000000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next ([2700000000000],
      [1500000000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next ([3450000000000], [2100000000000])
      (some (6, 7, 3)) (some (6, 7, 3)) (.next ([2700000000000, 9000000000000], [2250000000000,
      -9000000000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next ([1050000000000], [900000000000])
      (some (6, 7, 3)) (some (6, 7, 3)) (.next ([2700000000000], [2625000000000]) (some (6, 7, 3))
      (some (6, 7, 3)) (.next ([2700000000000, 9000000000000], [2850000000000]) (some (6, 7, 3))
      (some (6, 7, 3)) (.next ([3450000000000], [4485000000000]) (some (6, 7, 3)) (some (6, 7, 3))
      (.next ([2100000000000], [2850000000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next
      ([2700000000000, 9000000000000], [5235000000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next
      ([1800000000000], [4575000000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next ([1140000000000],
      [3435000000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next ([750000000000], [2700000000000])
      (some (6, 7, 3)) (some (6, 7, 3)) (.next ([375000000000], [1425000000000]) (some (6, 7, 3))
      (some (6, 7, 3)) fan24Owner4Part0)))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_6 : ExcludedOn (model24.B 6 ++ [step24.q]) 9000000000000 (model24.caps 6)
    (model24.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_7 : ExcludedOn (model24.B 7 ++ [step24.q]) 9000000000000 (model24.caps 7)
    (model24.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_8 : ExcludedOn (model24.B 8 ++ [step24.q]) 9000000000000 (model24.caps 8)
    (model24.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_9 : ExcludedOn (model24.B 9 ++ [step24.q]) 9000000000000 (model24.caps 9)
    (model24.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked24 : StepValid model24 9000000000000 step24 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded24_0
    · exact excluded24_1
    · exact excluded24_2
    · exact excluded24_3
    · exact excluded24_4
    · exact (hj rfl).elim
    · exact excluded24_6
    · exact excluded24_7
    · exact excluded24_8
    · exact excluded24_9
theorem next24 : model24.insert step24 = model25 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded25_1 : ExcludedOn (model25.B 1 ++ [step25.q]) 9000000000000 (model25.caps 1)
    (model25.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7950000000000, 9000000000000], [900000000000,
      -9000000000000]) none none (.next ([5250000000000], [3600000000000]) none none (.next
      ([2700000000000, 9000000000000], [2700000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([2550000000000, -9000000000000], [3600000000000, 0]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([0, 0], [2700000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-900000000000, 9000000000000], [8850000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-3600000000000], [8850000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2700000000000,
      -9000000000000], [5400000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-3600000000000, 0], [6150000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.terminal (some (3, 1, 0)) none none))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_2 : ExcludedOn (model25.B 2 ++ [step25.q]) 9000000000000 (model25.caps 2)
    (model25.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3600000000000], [150000000000]) (some (0, 3, 1))
      (some (0, 3, 1)) (.next ([6300000000000, -9000000000000], [2700000000000, 9000000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2550000000000, -9000000000000], [3600000000000, 0])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([900000000000, -9000000000000], [2850000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [2700000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-150000000000], [3750000000000])
      (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-2700000000000, -9000000000000], [9000000000000,
      0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3600000000000, 0], [6150000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2850000000000, -9000000000000],
      [3750000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_3 : ExcludedOn (model25.B 3 ++ [step25.q]) 9000000000000 (model25.caps 3)
    (model25.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3750000000000], [525000000000]) (some (3, 0, 5))
      (some (4, 0, 5)) fan25Owner3Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_4 : ExcludedOn (model25.B 4 ++ [step25.q]) 9000000000000 (model25.caps 4)
    (model25.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_5 : ExcludedOn (model25.B 5 ++ [step25.q]) 9000000000000 (model25.caps 5)
    (model25.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_6 : ExcludedOn (model25.B 6 ++ [step25.q]) 9000000000000 (model25.caps 6)
    (model25.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_7 : ExcludedOn (model25.B 7 ++ [step25.q]) 9000000000000 (model25.caps 7)
    (model25.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_8 : ExcludedOn (model25.B 8 ++ [step25.q]) 9000000000000 (model25.caps 8)
    (model25.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_9 : ExcludedOn (model25.B 9 ++ [step25.q]) 9000000000000 (model25.caps 9)
    (model25.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked25 : StepValid model25 9000000000000 step25 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded25_1
    · exact excluded25_2
    · exact excluded25_3
    · exact excluded25_4
    · exact excluded25_5
    · exact excluded25_6
    · exact excluded25_7
    · exact excluded25_8
    · exact excluded25_9
theorem next25 : model25.insert step25 = model26 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded26_0 : ExcludedOn (model26.B 0 ++ [step26.q]) 9000000000000 (model26.caps 0)
    (model26.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_1 : ExcludedOn (model26.B 1 ++ [step26.q]) 9000000000000 (model26.caps 1)
    (model26.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_2 : ExcludedOn (model26.B 2 ++ [step26.q]) 9000000000000 (model26.caps 2)
    (model26.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_3 : ExcludedOn (model26.B 3 ++ [step26.q]) 9000000000000 (model26.caps 3)
    (model26.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_4 : ExcludedOn (model26.B 4 ++ [step26.q]) 9000000000000 (model26.caps 4)
    (model26.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_6 : ExcludedOn (model26.B 6 ++ [step26.q]) 9000000000000 (model26.caps 6)
    (model26.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3150000000000], [300000000000]) (some (0, 5, 2))
      (some (0, 5, 3)) (.next ([4350000000000], [900000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([6075000000000], [1575000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([4575000000000], [1800000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([2700000000000, 9000000000000], [2700000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5,
      3)) (.next ([1800000000000, 9000000000000], [2550000000000, -9000000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([1125000000000, 0], [2250000000000, -9000000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([1650000000000, -9000000000000], [3600000000000, 9000000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1875000000000, -9000000000000], [4500000000000,
      9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([900000000000, 9000000000000],
      [3675000000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1125000000000],
      [4950000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0], [2700000000000,
      9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-300000000000], [3450000000000])
      (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-900000000000], [5250000000000]) (some (0, 2, 3))
      (some (5, 2, 3)) (.next ([-1575000000000, -9000000000000], [7650000000000, 9000000000000])
      (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-1800000000000], [6375000000000]) (some (5, 2, 3))
      (some (5, 2, 3)) (.next ([-2700000000000, -9000000000000], [5400000000000, 18000000000000])
      (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-2550000000000, 9000000000000], [4350000000000])
      (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-2250000000000, 9000000000000], [3375000000000,
      -9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-3600000000000, -9000000000000],
      [5250000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-4500000000000, -9000000000000],
      [6375000000000]) (some (5, 2, 3)) (some (5, 2, 4)) (.next ([-3675000000000, 9000000000000],
      [4575000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-4950000000000], [6075000000000])
      (some (5, 2, 4)) (some (5, 2, 0)) (.terminal (some (5, 2, 0)) (some (5, 2, 0)) (some (5, 2,
      0))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded26_7 : ExcludedOn (model26.B 7 ++ [step26.q]) 9000000000000 (model26.caps 7)
    (model26.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_8 : ExcludedOn (model26.B 8 ++ [step26.q]) 9000000000000 (model26.caps 8)
    (model26.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_9 : ExcludedOn (model26.B 9 ++ [step26.q]) 9000000000000 (model26.caps 9)
    (model26.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4050000000000], [600000000000]) (some (3, 0, 1))
      (some (3, 1, 2)) (.next ([2775000000000, -9000000000000], [2700000000000, 9000000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([4050000000000], [6075000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([1350000000000, -9000000000000], [6075000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([0], [5475000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next
      ([-600000000000], [4650000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([-2700000000000,
      -9000000000000], [5475000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-6075000000000],
      [10125000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-6075000000000], [7425000000000,
      -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1, 3)) (some (0, 1,
      3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked26 : StepValid model26 9000000000000 step26 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded26_0
    · exact excluded26_1
    · exact excluded26_2
    · exact excluded26_3
    · exact excluded26_4
    · exact (hj rfl).elim
    · exact excluded26_6
    · exact excluded26_7
    · exact excluded26_8
    · exact excluded26_9
theorem next26 : model26.insert step26 = model27 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded27_0 : ExcludedOn (model27.B 0 ++ [step27.q]) 9000000000000 (model27.caps 0)
    (model27.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_1 : ExcludedOn (model27.B 1 ++ [step27.q]) 9000000000000 (model27.caps 1)
    (model27.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_2 : ExcludedOn (model27.B 2 ++ [step27.q]) 9000000000000 (model27.caps 2)
    (model27.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_3 : ExcludedOn (model27.B 3 ++ [step27.q]) 9000000000000 (model27.caps 3)
    (model27.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_4 : ExcludedOn (model27.B 4 ++ [step27.q]) 9000000000000 (model27.caps 4)
    (model27.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_6 : ExcludedOn (model27.B 6 ++ [step27.q]) 9000000000000 (model27.caps 6)
    (model27.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3300000000000], [375000000000]) (some (0, 5, 2))
      (some (0, 5, 3)) (.next ([4350000000000], [900000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([6000000000000], [1800000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([4575000000000], [1800000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([2700000000000, 9000000000000], [2700000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5,
      3)) (.next ([1800000000000, 9000000000000], [2550000000000, -9000000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([1650000000000, -9000000000000], [3600000000000, 9000000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([1875000000000, -9000000000000], [4500000000000,
      9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([900000000000, 9000000000000],
      [3675000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 1, 3)) (.next ([750000000000],
      [3450000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([900000000000], [5100000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0], [2700000000000, 9000000000000]) (some (0, 1,
      3)) (some (0, 1, 3)) (.next ([-375000000000], [3675000000000]) (some (0, 1, 3)) (some (0, 2,
      3)) (.next ([-900000000000], [5250000000000]) (some (0, 2, 3)) (some (5, 2, 3)) (.next
      ([-1800000000000, -9000000000000], [7800000000000, 9000000000000]) (some (5, 2, 3)) (some (5,
      2, 3)) (.next ([-1800000000000], [6375000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-2700000000000, -9000000000000], [5400000000000, 18000000000000]) (some (5, 2, 3)) (some (5,
      2, 3)) (.next ([-2550000000000, 9000000000000], [4350000000000]) (some (5, 2, 3)) (some (5, 2,
      3)) (.next ([-3600000000000, -9000000000000], [5250000000000]) (some (5, 2, 3)) (some (5, 2,
      3)) (.next ([-4500000000000, -9000000000000], [6375000000000]) (some (5, 2, 3)) (some (5, 2,
      4)) (.next ([-3675000000000, 9000000000000], [4575000000000]) (some (5, 2, 4)) (some (5, 2,
      4)) (.next ([-3450000000000], [4200000000000]) (some (5, 2, 4)) (some (5, 2, 0)) (.next
      ([-5100000000000], [6000000000000]) (some (5, 2, 0)) (some (5, 2, 0)) (.terminal (some (5, 2,
      0)) (some (5, 2, 0)) (some (5, 2, 0))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_7 : ExcludedOn (model27.B 7 ++ [step27.q]) 9000000000000 (model27.caps 7)
    (model27.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_8 : ExcludedOn (model27.B 8 ++ [step27.q]) 9000000000000 (model27.caps 8)
    (model27.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_9 : ExcludedOn (model27.B 9 ++ [step27.q]) 9000000000000 (model27.caps 9)
    (model27.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3900000000000], [525000000000]) (some (3, 0, 1))
      (some (3, 1, 2)) (.next ([2775000000000, -9000000000000], [2700000000000, 9000000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([3900000000000], [6000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([1200000000000, -9000000000000], [6000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([0], [5475000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next
      ([-525000000000], [4425000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([-2700000000000,
      -9000000000000], [5475000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-6000000000000],
      [9900000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-6000000000000], [7200000000000,
      -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1, 3)) (some (0, 1,
      3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked27 : StepValid model27 9000000000000 step27 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded27_0
    · exact excluded27_1
    · exact excluded27_2
    · exact excluded27_3
    · exact excluded27_4
    · exact (hj rfl).elim
    · exact excluded27_6
    · exact excluded27_7
    · exact excluded27_8
    · exact excluded27_9
theorem next27 : model27.insert step27 = model28 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded28_0 : ExcludedOn (model28.B 0 ++ [step28.q]) 9000000000000 (model28.caps 0)
    (model28.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_1 : ExcludedOn (model28.B 1 ++ [step28.q]) 9000000000000 (model28.caps 1)
    (model28.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_2 : ExcludedOn (model28.B 2 ++ [step28.q]) 9000000000000 (model28.caps 2)
    (model28.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_3 : ExcludedOn (model28.B 3 ++ [step28.q]) 9000000000000 (model28.caps 3)
    (model28.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_5 : ExcludedOn (model28.B 5 ++ [step28.q]) 9000000000000 (model28.caps 5)
    (model28.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_6 : ExcludedOn (model28.B 6 ++ [step28.q]) 9000000000000 (model28.caps 6)
    (model28.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_7 : ExcludedOn (model28.B 7 ++ [step28.q]) 9000000000000 (model28.caps 7)
    (model28.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_8 : ExcludedOn (model28.B 8 ++ [step28.q]) 9000000000000 (model28.caps 8)
    (model28.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4875000000000], [2400000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([5550000000000], [3450000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([1725000000000], [1725000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1425000000000], [4125000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [7275000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2400000000000], [7275000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3450000000000], [9000000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-1725000000000], [3450000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-4125000000000], [5550000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded28_9 : ExcludedOn (model28.B 9 ++ [step28.q]) 9000000000000 (model28.caps 9)
    (model28.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked28 : StepValid model28 9000000000000 step28 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded28_0
    · exact excluded28_1
    · exact excluded28_2
    · exact excluded28_3
    · exact (hj rfl).elim
    · exact excluded28_5
    · exact excluded28_6
    · exact excluded28_7
    · exact excluded28_8
    · exact excluded28_9
theorem next28 : model28.insert step28 = model29 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded29_0 : ExcludedOn (model29.B 0 ++ [step29.q]) 9000000000000 (model29.caps 0)
    (model29.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_1 : ExcludedOn (model29.B 1 ++ [step29.q]) 9000000000000 (model29.caps 1)
    (model29.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_2 : ExcludedOn (model29.B 2 ++ [step29.q]) 9000000000000 (model29.caps 2)
    (model29.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_3 : ExcludedOn (model29.B 3 ++ [step29.q]) 9000000000000 (model29.caps 3)
    (model29.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_5 : ExcludedOn (model29.B 5 ++ [step29.q]) 9000000000000 (model29.caps 5)
    (model29.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5025000000000], [1365000000000]) (some (5, 0,
      3)) (some (5, 1, 3)) (.next ([3000000000000], [900000000000]) (some (5, 1, 3)) (some (6, 1,
      3)) (.next ([2925000000000], [1125000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
      ([150000000000], [75000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([5025000000000, 0],
      [2700000000000, 9000000000000]) (some (6, 1, 3)) (some (6, 1, 4)) (.next ([3765000000000],
      [2625000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3765000000000, 0], [2700000000000,
      9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3690000000000, -9000000000000],
      [2700000000000, 9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([4125000000000],
      [3900000000000]) (some (6, 1, 4)) (some (6, 1, 4)) fan29Owner5Part0)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel)
      0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded29_6 : ExcludedOn (model29.B 6 ++ [step29.q]) 9000000000000 (model29.caps 6)
    (model29.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_7 : ExcludedOn (model29.B 7 ++ [step29.q]) 9000000000000 (model29.caps 7)
    (model29.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_8 : ExcludedOn (model29.B 8 ++ [step29.q]) 9000000000000 (model29.caps 8)
    (model29.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_9 : ExcludedOn (model29.B 9 ++ [step29.q]) 9000000000000 (model29.caps 9)
    (model29.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked29 : StepValid model29 9000000000000 step29 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded29_0
    · exact excluded29_1
    · exact excluded29_2
    · exact excluded29_3
    · exact (hj rfl).elim
    · exact excluded29_5
    · exact excluded29_6
    · exact excluded29_7
    · exact excluded29_8
    · exact excluded29_9
theorem next29 : model29.insert step29 = model30 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded30_0 : ExcludedOn (model30.B 0 ++ [step30.q]) 9000000000000 (model30.caps 0)
    (model30.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_1 : ExcludedOn (model30.B 1 ++ [step30.q]) 9000000000000 (model30.caps 1)
    (model30.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_2 : ExcludedOn (model30.B 2 ++ [step30.q]) 9000000000000 (model30.caps 2)
    (model30.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_3 : ExcludedOn (model30.B 3 ++ [step30.q]) 9000000000000 (model30.caps 3)
    (model30.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_5 : ExcludedOn (model30.B 5 ++ [step30.q]) 9000000000000 (model30.caps 5)
    (model30.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5400000000000, 0], [900000000000,
      9000000000000]) (some (5, 0, 3)) (some (5, 1, 3)) (.next ([3600000000000], [990000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([3000000000000], [900000000000]) (some (5, 1, 3))
      (some (6, 1, 3)) (.next ([2925000000000], [1125000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      (.next ([4500000000000], [2100000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
      ([150000000000], [75000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4275000000000],
      [2250000000000]) (some (6, 1, 3)) (some (6, 1, 4)) (.next ([3765000000000], [2625000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3765000000000, 0], [2700000000000, 9000000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3690000000000, -9000000000000], [2700000000000,
      9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([2490000000000], [3000000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([2340000000000], [2925000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) (.next ([2865000000000], [3900000000000]) (some (6, 1, 4)) (some (6, 1, 5))
      fan30Owner5Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded30_6 : ExcludedOn (model30.B 6 ++ [step30.q]) 9000000000000 (model30.caps 6)
    (model30.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_7 : ExcludedOn (model30.B 7 ++ [step30.q]) 9000000000000 (model30.caps 7)
    (model30.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_8 : ExcludedOn (model30.B 8 ++ [step30.q]) 9000000000000 (model30.caps 8)
    (model30.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_9 : ExcludedOn (model30.B 9 ++ [step30.q]) 9000000000000 (model30.caps 9)
    (model30.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked30 : StepValid model30 9000000000000 step30 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded30_0
    · exact excluded30_1
    · exact excluded30_2
    · exact excluded30_3
    · exact (hj rfl).elim
    · exact excluded30_5
    · exact excluded30_6
    · exact excluded30_7
    · exact excluded30_8
    · exact excluded30_9
theorem next30 : model30.insert step30 = model31 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded31_0 : ExcludedOn (model31.B 0 ++ [step31.q]) 9000000000000 (model31.caps 0)
    (model31.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_1 : ExcludedOn (model31.B 1 ++ [step31.q]) 9000000000000 (model31.caps 1)
    (model31.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_2 : ExcludedOn (model31.B 2 ++ [step31.q]) 9000000000000 (model31.caps 2)
    (model31.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_3 : ExcludedOn (model31.B 3 ++ [step31.q]) 9000000000000 (model31.caps 3)
    (model31.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_5 : ExcludedOn (model31.B 5 ++ [step31.q]) 9000000000000 (model31.caps 5)
    (model31.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5850000000000, 0], [0, 9000000000000]) (some (5,
      0, 3)) (some (5, 1, 3)) (.next ([3150000000000], [540000000000]) (some (5, 1, 3)) (some (5, 1,
      3)) (.next ([4950000000000], [1200000000000]) (some (5, 1, 3)) (some (6, 1, 3)) (.next
      ([4725000000000], [1350000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([3000000000000],
      [900000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([2925000000000], [1125000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([150000000000], [75000000000]) (some (6, 1, 3))
      (some (6, 1, 3)) (.next ([3765000000000], [2625000000000]) (some (6, 1, 3)) (some (6, 1, 4))
      (.next ([3765000000000, 0], [2700000000000, 9000000000000]) (some (6, 1, 4)) (some (6, 1, 4))
      (.next ([3690000000000, -9000000000000], [2700000000000, 9000000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) (.next ([2700000000000], [3150000000000]) (some (6, 1, 4)) (some (6, 1, 4))
      fan31Owner5Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded31_6 : ExcludedOn (model31.B 6 ++ [step31.q]) 9000000000000 (model31.caps 6)
    (model31.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_7 : ExcludedOn (model31.B 7 ++ [step31.q]) 9000000000000 (model31.caps 7)
    (model31.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_8 : ExcludedOn (model31.B 8 ++ [step31.q]) 9000000000000 (model31.caps 8)
    (model31.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_9 : ExcludedOn (model31.B 9 ++ [step31.q]) 9000000000000 (model31.caps 9)
    (model31.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked31 : StepValid model31 9000000000000 step31 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded31_0
    · exact excluded31_1
    · exact excluded31_2
    · exact excluded31_3
    · exact (hj rfl).elim
    · exact excluded31_5
    · exact excluded31_6
    · exact excluded31_7
    · exact excluded31_8
    · exact excluded31_9
theorem next31 : model31.insert step31 = model32 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint300000310000
end ConwaySoifer.Simplified.Certificates
