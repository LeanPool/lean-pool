/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint110000120000
import Mathlib.Tactic.FinCases

/-!
# Sint 110000 120000 4

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
namespace Sint110000120000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner5Part0 : FanWitness := (.next ([4260000000000], [990000000000]) (some (0, 1, 5)) (some
    (0, 1, 5)) (.next ([2010000000000, -9000000000000], [660000000000]) (some (0, 1, 5)) (some (0,
    1, 5)) (.next ([3150000000000, -9000000000000], [1890000000000, 9000000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([3270000000000, -9000000000000], [1980000000000, 9000000000000]) (some
    (0, 1, 5)) (some (0, 1, 5)) (.next ([5340000000000], [3660000000000]) (some (0, 1, 5)) (some (0,
    1, 5)) (.next ([120000000000], [90000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([960000000000], [4140000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([750000000000],
    [4260000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([600000000000], [3990000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([480000000000], [3900000000000]) (some (0, 1, 4))
    (some (0, 1, 4)) (.next ([0], [6000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
    ([-990000000000, -9000000000000], [6990000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 2,
    4)) (.next ([-900000000000], [5040000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-660000000000], [3660000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-990000000000],
    [5250000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-660000000000, 0], [2670000000000,
    -9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1890000000000, -9000000000000],
    [5040000000000]) (some (0, 2, 4)) (some (0, 5, 4)) (.next ([-1980000000000, -9000000000000],
    [5250000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3660000000000], [9000000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-90000000000], [210000000000]) (some (0, 5, 4)) (some
    (0, 5, 4)) (.next ([-4140000000000], [5100000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-4260000000000], [5010000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3990000000000],
    [4590000000000]) (some (0, 5, 0)) (some (0, 5, 0)) (.next ([-3900000000000], [4380000000000])
    (some (0, 5, 0)) (some (0, 5, 0)) (.terminal (some (0, 5, 0)) (some (0, 5, 0)) (some (0, 5,
    0)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner4Part0 : FanWitness := (.next ([7260000000000, -9000000000000], [1080000000000,
    9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([6000000000000, 0], [990000000000,
    9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([3375000000000], [660000000000]) (some
    (4, 1, 5)) (some (4, 1, 5)) (.next ([4260000000000], [1080000000000]) (some (4, 1, 5)) (some (4,
    1, 5)) (.next ([5910000000000], [2340000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([1035000000000], [615000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2385000000000,
    -9000000000000], [1650000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([3000000000000], [3990000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1965000000000],
    [3375000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([990000000000], [3000000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([570000000000], [4305000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([0, 0], [990000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1,
    5)) (.next ([-90000000000], [8340000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-1080000000000, -9000000000000], [8340000000000, 0]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
    ([-990000000000, -9000000000000], [6990000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2,
    5)) (.next ([-660000000000], [4035000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1080000000000], [5340000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2340000000000],
    [8250000000000]) (some (0, 2, 5)) (some (0, 5, 5)) (.next ([-615000000000], [1650000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-1650000000000, -9000000000000], [4035000000000, 0])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3990000000000], [6990000000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.next ([-3375000000000], [5340000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-3000000000000], [3990000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-4305000000000], [4875000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5,
    4)) (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner5Part0 : FanWitness := (.next ([4260000000000], [990000000000]) (some (5, 1, 2)) (some
    (5, 1, 2)) (.next ([7350000000000, -9000000000000], [1740000000000, 9000000000000]) (some (5, 1,
    2)) (some (5, 1, 2)) (.next ([5250000000000], [3090000000000]) (some (5, 1, 2)) (some (5, 1, 5))
    (.next ([3150000000000, -9000000000000], [1890000000000, 9000000000000]) (some (0, 1, 5)) (some
    (0, 1, 5)) (.next ([3270000000000, -9000000000000], [1980000000000, 9000000000000]) (some (0, 1,
    5)) (some (0, 1, 5)) (.next ([120000000000], [90000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([960000000000], [4140000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([750000000000], [4260000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([240000000000],
    [3840000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([150000000000], [4050000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0], [6000000000000]) (some (0, 1, 5)) (some (0, 1,
    5)) (.next ([-750000000000], [9090000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
    ([-990000000000, -9000000000000], [6990000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2,
    5)) (.next ([-900000000000], [5040000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-990000000000], [5250000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1740000000000,
    -9000000000000], [9090000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3090000000000],
    [8340000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1890000000000, -9000000000000],
    [5040000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1980000000000, -9000000000000],
    [5250000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-90000000000], [210000000000]) (some
    (0, 2, 5)) (some (0, 2, 5)) (.next ([-4140000000000], [5100000000000]) (some (0, 2, 5)) (some
    (0, 2, 5)) (.next ([-4260000000000], [5010000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-3840000000000], [4080000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4050000000000],
    [4200000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2, 5))
    (some (0, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner6Part0 : FanWitness := (.next ([3270000000000, -9000000000000], [1980000000000,
    9000000000000]) (some (5, 0, 3)) (some (5, 0, 3)) (.next ([5625000000000], [3705000000000])
    (some (5, 0, 3)) (some (5, 0, 3)) (.next ([990000000000, 9000000000000], [990000000000,
    9000000000000]) (some (5, 0, 3)) (some (5, 0, 3)) (.next ([4635000000000, -9000000000000],
    [4695000000000, 9000000000000]) (some (5, 0, 3)) (some (5, 0, 3)) (.next ([1365000000000],
    [2715000000000]) (some (5, 0, 3)) (some (5, 0, 3)) (.next ([1635000000000], [3330000000000])
    (some (5, 0, 3)) (some (5, 0, 3)) (.next ([750000000000], [3600000000000]) (some (5, 0, 3))
    (some (5, 0, 3)) (.next ([660000000000, 0], [4350000000000, -9000000000000]) (some (5, 0, 3))
    (some (5, 0, 3)) (.next ([660000000000], [5340000000000]) (some (5, 0, 3)) (some (5, 1, 3))
    (.next ([0, 9000000000000], [4260000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([0, 0], [990000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([-330000000000, -9000000000000], [6330000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 2,
    3)) (.next ([-990000000000], [5250000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
    ([-2715000000000, 9000000000000], [8340000000000, -9000000000000]) (some (5, 2, 3)) (some (5, 2,
    3)) (.next ([-1980000000000, -9000000000000], [5250000000000]) (some (5, 2, 3)) (some (5, 2, 3))
    (.next ([-3705000000000], [9330000000000]) (some (5, 2, 3)) (some (5, 2, 4)) (.next
    ([-990000000000, -9000000000000], [1980000000000, 18000000000000]) (some (5, 2, 4)) (some (5, 2,
    4)) (.next ([-4695000000000, -9000000000000], [9330000000000]) (some (5, 2, 4)) (some (5, 2, 4))
    (.next ([-2715000000000], [4080000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
    ([-3330000000000], [4965000000000]) (some (5, 2, 4)) (some (5, 2, 5)) (.next ([-3600000000000],
    [4350000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4350000000000, 9000000000000],
    [5010000000000, -9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5340000000000],
    [6000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4260000000000, 9000000000000],
    [4260000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2, 5))
    (some (0, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner6Part0 : FanWitness := (.next ([1080000000000, 0], [3930000000000, -9000000000000])
    (some (4, 0, 6)) (some (4, 0, 6)) (.next ([750000000000], [3180000000000]) (some (4, 0, 6))
    (some (4, 0, 6)) (.next ([1080000000000], [4920000000000]) (some (4, 0, 6)) (some (5, 0, 6))
    (.next ([750000000000], [3600000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
    ([765000000000], [4485000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([660000000000, 0],
    [4350000000000, -9000000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([660000000000],
    [5340000000000]) (some (5, 0, 6)) (some (5, 1, 6)) (.next ([0, 9000000000000], [4260000000000,
    -9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0], [420000000000]) (some (5, 1, 6))
    (some (5, 1, 6)) (.next ([-330000000000, -9000000000000], [6330000000000, 9000000000000]) (some
    (0, 1, 6)) (some (0, 2, 6)) (.next ([-990000000000], [5250000000000]) (some (0, 2, 6)) (some (0,
    2, 6)) (.next ([-2415000000000], [8415000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-2835000000000], [8835000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1980000000000,
    -9000000000000], [5250000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-990000000000,
    -9000000000000], [1980000000000, 18000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-3495000000000, 0], [4485000000000, 9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-3930000000000, 9000000000000], [5010000000000, -9000000000000]) (some (0, 2, 6)) (some (0, 2,
    6)) (.next ([-3180000000000], [3930000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-4920000000000], [6000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-3600000000000],
    [4350000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-4485000000000], [5250000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-4350000000000, 9000000000000], [5010000000000,
    -9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-5340000000000], [6000000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4260000000000, 9000000000000], [4260000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2,
    4)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_1 : ExcludedOn (model32.B 1 ++ [step32.q]) 9000000000000 (model32.caps 1)
    (model32.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_2 : ExcludedOn (model32.B 2 ++ [step32.q]) 9000000000000 (model32.caps 2)
    (model32.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6000000000000, 0], [990000000000,
      9000000000000]) (some (0, 0, 5)) (some (0, 1, 5)) (.next ([4140000000000], [900000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([3000000000000], [660000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) fan32Owner5Part0)))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded32_7 : ExcludedOn (model32.B 7 ++ [step32.q]) 9000000000000 (model32.caps 7)
    (model32.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_8 : ExcludedOn (model32.B 8 ++ [step32.q]) 9000000000000 (model32.caps 8)
    (model32.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_9 : ExcludedOn (model32.B 9 ++ [step32.q]) 9000000000000 (model32.caps 9)
    (model32.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4200000000000], [1800000000000]) (some (4, 1,
      2)) (some (4, 2, 3)) (.next ([3660000000000], [3420000000000]) (some (4, 2, 3)) (some (4, 2,
      3)) (.next ([3660000000000], [6000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([750000000000], [1830000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([1830000000000],
      [6000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([30000000000], [3420000000000])
      (some (4, 2, 3)) (some (4, 2, 4)) (.next ([30000000000], [6000000000000]) (some (4, 2, 4))
      (some (4, 2, 4)) (.next ([0], [3630000000000]) (some (4, 2, 4)) (some (4, 2, 4)) (.next
      ([-1800000000000], [6000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-3420000000000], [7080000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-6000000000000], [9660000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-1830000000000], [2580000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-6000000000000], [7830000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-3420000000000], [3450000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-6000000000000], [6030000000000]) (some (0, 2, 4)) (some (1, 2, 4)) (.terminal (some (1, 2,
      4)) (some (1, 2, 4)) (some (1, 2, 4))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded32_3
    · exact excluded32_4
    · exact excluded32_5
    · exact (hj rfl).elim
    · exact excluded32_7
    · exact excluded32_8
    · exact excluded32_9
theorem next32 : model32.insert step32 = model33 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded33_0 : ExcludedOn (model33.B 0 ++ [step33.q]) 9000000000000 (model33.caps 0)
    (model33.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_1 : ExcludedOn (model33.B 1 ++ [step33.q]) 9000000000000 (model33.caps 1)
    (model33.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1485000000000, 0], [240000000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next ([525000000000], [225000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([5250000000000], [3480000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([1260000000000, 0], [990000000000, 9000000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([4500000000000], [4005000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([5250000000000], [4740000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([750000000000], [735000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([4260000000000,
      -9000000000000], [5730000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([0,
      0], [990000000000, 9000000000000]) (some (0, 4, 3)) (some (4, 4, 3)) (.next ([-240000000000,
      -9000000000000], [1725000000000, 9000000000000]) (some (4, 4, 0)) (some (4, 4, 0)) (.next
      ([-225000000000], [750000000000]) (some (4, 4, 0)) (some (4, 4, 0)) (.next ([-3480000000000],
      [8730000000000]) (some (4, 4, 0)) (some (4, 4, 0)) (.next ([-990000000000, -9000000000000],
      [2250000000000, 9000000000000]) (some (4, 2, 0)) (some (4, 2, 0)) (.next ([-4005000000000],
      [8505000000000]) (some (4, 2, 0)) (some (4, 2, 0)) (.next ([-4740000000000], [9990000000000])
      (some (4, 2, 0)) (some (4, 2, 0)) (.next ([-735000000000], [1485000000000]) (some (4, 2, 0))
      (some (4, 2, 0)) (.next ([-5730000000000, -9000000000000], [9990000000000, 0]) (some (4, 2,
      0)) (some (4, 2, 0)) (.terminal (some (4, 2, 0)) (some (4, 2, 0)) (some (4, 2,
      0))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded33_2 : ExcludedOn (model33.B 2 ++ [step33.q]) 9000000000000 (model33.caps 2)
    (model33.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded34_1 : ExcludedOn (model34.B 1 ++ [step34.q]) 9000000000000 (model34.caps 1)
    (model34.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_3 : ExcludedOn (model34.B 3 ++ [step34.q]) 9000000000000 (model34.caps 3)
    (model34.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7545000000000], [330000000000]) (some (2, 0, 4))
      (some (3, 0, 4)) (.next ([7785000000000], [1125000000000]) (some (3, 0, 4)) (some (3, 4, 4))
      (.next ([6750000000000], [1365000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([990000000000], [375000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([660000000000],
      [8250000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0], [990000000000, 9000000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-330000000000], [7875000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-1125000000000], [8910000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([-1365000000000], [8115000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-375000000000], [1365000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-8250000000000],
      [8910000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.terminal (some (0, 4, 2)) (some (0, 4,
      2)) (some (0, 4, 2))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_4 : ExcludedOn (model34.B 4 ++ [step34.q]) 9000000000000 (model34.caps 4)
    (model34.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8250000000000], [90000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) fan34Owner4Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8340000000000], [750000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([6000000000000, 0], [990000000000, 9000000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([4140000000000], [900000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      fan34Owner5Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded35_0 : ExcludedOn (model35.B 0 ++ [step35.q]) 9000000000000 (model35.caps 0)
    (model35.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_1 : ExcludedOn (model35.B 1 ++ [step35.q]) 9000000000000 (model35.caps 1)
    (model35.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_2 : ExcludedOn (model35.B 2 ++ [step35.q]) 9000000000000 (model35.caps 2)
    (model35.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_3 : ExcludedOn (model35.B 3 ++ [step35.q]) 9000000000000 (model35.caps 3)
    (model35.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_4 : ExcludedOn (model35.B 4 ++ [step35.q]) 9000000000000 (model35.caps 4)
    (model35.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_6 : ExcludedOn (model35.B 6 ++ [step35.q]) 9000000000000 (model35.caps 6)
    (model35.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6000000000000], [330000000000, 9000000000000])
      (some (5, 0, 2)) (some (5, 0, 3)) (.next ([4260000000000], [990000000000]) (some (5, 0, 3))
      (some (5, 0, 3)) (.next ([5625000000000, 0], [2715000000000, -9000000000000]) (some (5, 0, 3))
      (some (5, 0, 3)) fan35Owner6Part0)))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded35_6
    · exact excluded35_7
    · exact excluded35_8
    · exact excluded35_9
theorem next35 : model35.insert step35 = model36 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded36_0 : ExcludedOn (model36.B 0 ++ [step36.q]) 9000000000000 (model36.caps 0)
    (model36.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_1 : ExcludedOn (model36.B 1 ++ [step36.q]) 9000000000000 (model36.caps 1)
    (model36.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_2 : ExcludedOn (model36.B 2 ++ [step36.q]) 9000000000000 (model36.caps 2)
    (model36.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_3 : ExcludedOn (model36.B 3 ++ [step36.q]) 9000000000000 (model36.caps 3)
    (model36.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_4 : ExcludedOn (model36.B 4 ++ [step36.q]) 9000000000000 (model36.caps 4)
    (model36.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5295000000000], [330000000000]) (some (0, 0, 4))
      (some (0, 1, 4)) (.next ([6000000000000, 0], [990000000000, 9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([4305000000000, -9000000000000], [1320000000000, 9000000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([3000000000000], [1080000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([2010000000000, -9000000000000], [1080000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([4920000000000], [4080000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([1215000000000], [3330000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([375000000000], [5295000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [6000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-330000000000], [5625000000000])
      (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-990000000000, -9000000000000], [6990000000000,
      9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1320000000000, -9000000000000],
      [5625000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1080000000000], [4080000000000])
      (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1080000000000, 0], [3090000000000,
      -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-4080000000000], [9000000000000])
      (some (0, 2, 3)) (some (0, 4, 3)) (.next ([-3330000000000], [4545000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-5295000000000], [5670000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.terminal (some (0, 4, 0)) (some (0, 4, 0)) (some (0, 4, 0))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4200000000000], [1800000000000]) (some (4, 1,
      2)) (some (4, 2, 3)) (.next ([4080000000000], [3420000000000]) (some (4, 2, 3)) (some (4, 2,
      3)) (.next ([4080000000000], [6000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([750000000000], [1830000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([2250000000000],
      [6000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([30000000000], [3420000000000])
      (some (4, 2, 3)) (some (4, 2, 4)) (.next ([30000000000], [6000000000000]) (some (4, 2, 4))
      (some (4, 2, 4)) (.next ([0], [4050000000000]) (some (4, 2, 4)) (some (4, 2, 4)) (.next
      ([-1800000000000], [6000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-3420000000000], [7500000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-6000000000000], [10080000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-1830000000000], [2580000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-6000000000000], [8250000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-3420000000000], [3450000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-6000000000000], [6030000000000]) (some (0, 2, 4)) (some (1, 2, 4)) (.terminal (some (1, 2,
      4)) (some (1, 2, 4)) (some (1, 2, 4))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded36_7
    · exact excluded36_8
    · exact excluded36_9
theorem next36 : model36.insert step36 = model37 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded37_0 : ExcludedOn (model37.B 0 ++ [step37.q]) 9000000000000 (model37.caps 0)
    (model37.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_2 : ExcludedOn (model37.B 2 ++ [step37.q]) 9000000000000 (model37.caps 2)
    (model37.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_3 : ExcludedOn (model37.B 3 ++ [step37.q]) 9000000000000 (model37.caps 3)
    (model37.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_4 : ExcludedOn (model37.B 4 ++ [step37.q]) 9000000000000 (model37.caps 4)
    (model37.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_5 : ExcludedOn (model37.B 5 ++ [step37.q]) 9000000000000 (model37.caps 5)
    (model37.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_6 : ExcludedOn (model37.B 6 ++ [step37.q]) 9000000000000 (model37.caps 6)
    (model37.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6000000000000], [330000000000, 9000000000000])
      (some (4, 0, 2)) (some (4, 0, 6)) (.next ([4260000000000], [990000000000]) (some (4, 0, 6))
      (some (4, 0, 6)) (.next ([6000000000000], [2415000000000]) (some (4, 0, 6)) (some (4, 0, 6))
      (.next ([6000000000000], [2835000000000]) (some (4, 0, 6)) (some (4, 0, 6)) (.next
      ([3270000000000, -9000000000000], [1980000000000, 9000000000000]) (some (4, 0, 6)) (some (4,
      0, 6)) (.next ([990000000000, 9000000000000], [990000000000, 9000000000000]) (some (4, 0, 6))
      (some (4, 0, 6)) (.next ([990000000000, 9000000000000], [3495000000000]) (some (4, 0, 6))
      (some (4, 0, 6)) fan37Owner6Part0)))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded37_2
    · exact excluded37_3
    · exact excluded37_4
    · exact excluded37_5
    · exact excluded37_6
    · exact excluded37_7
    · exact excluded37_8
    · exact excluded37_9
theorem next37 : model37.insert step37 = model38 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded38_1 : ExcludedOn (model38.B 1 ++ [step38.q]) 9000000000000 (model38.caps 1)
    (model38.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_2 : ExcludedOn (model38.B 2 ++ [step38.q]) 9000000000000 (model38.caps 2)
    (model38.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8010000000000, -9000000000000], [990000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4260000000000, -9000000000000],
      [1320000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1320000000000],
      [2430000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([330000000000, -9000000000000],
      [3420000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0],
      [990000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-990000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next
      ([-1320000000000, 0], [5580000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-2430000000000], [3750000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-3420000000000, -9000000000000], [3750000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.terminal (some (0, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded38_3 : ExcludedOn (model38.B 3 ++ [step38.q]) 9000000000000 (model38.caps 3)
    (model38.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_4 : ExcludedOn (model38.B 4 ++ [step38.q]) 9000000000000 (model38.caps 4)
    (model38.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_5 : ExcludedOn (model38.B 5 ++ [step38.q]) 9000000000000 (model38.caps 5)
    (model38.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_6 : ExcludedOn (model38.B 6 ++ [step38.q]) 9000000000000 (model38.caps 6)
    (model38.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_7 : ExcludedOn (model38.B 7 ++ [step38.q]) 9000000000000 (model38.caps 7)
    (model38.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded38_1
    · exact excluded38_2
    · exact excluded38_3
    · exact excluded38_4
    · exact excluded38_5
    · exact excluded38_6
    · exact excluded38_7
    · exact excluded38_8
    · exact excluded38_9
theorem next38 : model38.insert step38 = model39 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint110000120000
end ConwaySoifer.Simplified.Certificates
