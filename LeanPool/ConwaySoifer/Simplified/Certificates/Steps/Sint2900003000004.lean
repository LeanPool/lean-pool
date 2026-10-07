/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint290000300000
import Mathlib.Tactic.FinCases

/-!
# Sint 290000 300000 4

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
namespace Sint290000300000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner4Part0 : FanWitness := (.next ([0], [2760000000000]) (some (6, 7, 4)) (some (6, 7, 4))
    (.next ([-33000000000], [1710000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
    ([-165000000000], [6360000000000]) (some (0, 7, 4)) (some (0, 7, 5)) (.next ([-135000000000],
    [3480000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-150000000000], [3750000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-15000000000], [270000000000]) (some (0, 7, 5)) (some
    (0, 7, 5)) (.next ([-1113000000000], [6375000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-1083000000000], [4698000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-1080000000000],
    [4665000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-2760000000000], [6345000000000])
    (some (0, 7, 5)) (some (0, 7, 6)) (.next ([-1995000000000], [3750000000000]) (some (0, 7, 6))
    (some (0, 7, 6)) (.next ([-1440000000000], [2625000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([-4605000000000], [8190000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-1980000000000], [3480000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-3480000000000],
    [6105000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-3750000000000], [6360000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-2760000000000], [4665000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-2928000000000], [4698000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([-1695000000000], [2610000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-4698000000000], [6375000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-948000000000],
    [1218000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-6105000000000], [6210000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-933000000000], [948000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-4605000000000], [4665000000000]) (some (0, 3, 6)) (some (0, 4, 6))
    (.terminal (some (0, 4, 6)) (some (0, 4, 6)) (some (0, 4, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner4Part0 : FanWitness := (.next ([105000000000], [6105000000000]) (some (6, 1, 7)) (some
    (6, 1, 7)) (.next ([15000000000], [933000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([0],
    [2760000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([-15000000000], [2610000000000])
    (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-30000000000], [1677000000000]) (some (0, 1, 7))
    (some (0, 1, 7)) (.next ([-33000000000], [1710000000000]) (some (0, 1, 7)) (some (0, 1, 7))
    (.next ([-165000000000], [6360000000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next
    ([-135000000000], [3480000000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-150000000000],
    [3750000000000]) (some (0, 1, 7)) (some (0, 2, 7)) (.next ([-15000000000], [270000000000]) (some
    (0, 2, 7)) (some (0, 2, 7)) (.next ([-1113000000000], [6375000000000]) (some (0, 2, 7)) (some
    (0, 3, 7)) (.next ([-1083000000000], [4698000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
    ([-1080000000000], [4665000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-2760000000000],
    [6345000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-1440000000000], [2625000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-3480000000000], [6105000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-3750000000000], [6360000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([-2760000000000], [4665000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-1695000000000], [2610000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-4698000000000],
    [6375000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-948000000000], [1218000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-2625000000000], [2865000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-6105000000000], [6210000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([-933000000000], [948000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.terminal (some (0,
    3, 6)) (some (0, 4, 6)) (some (0, 4, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner0Part0 : FanWitness := (.next ([375000000000], [225000000000]) (some (4, 0, 5)) (some
    (4, 0, 5)) (.next ([2610000000000], [2805000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
    ([3195000000000], [3690000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([1440000000000],
    [1935000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([3525000000000], [4875000000000])
    (some (4, 0, 5)) (some (4, 1, 5)) (.next ([585000000000], [885000000000]) (some (4, 1, 5)) (some
    (4, 1, 5)) (.next ([2925000000000], [5250000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([555000000000], [3405000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([150000000000],
    [6315000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-450000000000], [6690000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-435000000000], [5430000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-420000000000], [3045000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-645000000000], [3645000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-1035000000000], [5805000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2250000000000],
    [8820000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-225000000000], [600000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2805000000000], [5415000000000]) (some (0, 1, 3))
    (some (0, 1, 4)) (.next ([-3690000000000], [6885000000000]) (some (0, 1, 4)) (some (0, 1, 4))
    (.next ([-1935000000000], [3375000000000]) (some (0, 1, 4)) (some (0, 5, 4)) (.next
    ([-4875000000000], [8400000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-885000000000],
    [1470000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-5250000000000], [8175000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3405000000000], [3960000000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.next ([-6315000000000], [6465000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.terminal (some (0, 5, 4)) (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan38Owner6Part0 : FanWitness := (.next ([1905000000000, -9000000000000], [4485000000000,
    9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([213000000000], [927000000000]) (some
    (5, 1, 3)) (some (5, 1, 3)) (.next ([525000000000], [4125000000000]) (some (5, 1, 3)) (some (5,
    1, 3)) (.next ([312000000000], [3198000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([45000000000], [690000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([105000000000],
    [4302000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0], [5355000000000]) (some (0, 1,
    3)) (some (0, 1, 3)) (.next ([-165000000000], [4860000000000]) (some (0, 1, 3)) (some (0, 2, 3))
    (.next ([-948000000000], [5250000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([-1035000000000], [4515000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1080000000000],
    [3825000000000]) (some (0, 2, 3)) (some (0, 2, 6)) (.next ([-477000000000], [1662000000000])
    (some (0, 2, 6)) (some (1, 2, 6)) (.next ([-1875000000000], [6390000000000]) (some (1, 2, 6))
    (some (1, 2, 6)) (.next ([-2610000000000, -9000000000000], [7965000000000, 9000000000000]) (some
    (1, 2, 6)) (some (1, 2, 6)) (.next ([-2610000000000], [6435000000000]) (some (1, 2, 6)) (some
    (1, 2, 6)) (.next ([-1740000000000], [3990000000000]) (some (1, 2, 6)) (some (1, 2, 6)) (.next
    ([-3990000000000], [7605000000000]) (some (1, 2, 6)) (some (1, 2, 6)) (.next ([-3558000000000,
    -9000000000000], [5250000000000]) (some (1, 2, 6)) (some (1, 2, 6)) (.next ([-4485000000000,
    -9000000000000], [6390000000000]) (some (1, 2, 6)) (some (1, 2, 6)) (.next ([-927000000000],
    [1140000000000]) (some (1, 2, 6)) (some (1, 2, 6)) (.next ([-4125000000000], [4650000000000])
    (some (1, 2, 6)) (some (1, 2, 6)) (.next ([-3198000000000], [3510000000000]) (some (1, 2, 5))
    (some (1, 2, 5)) (.next ([-690000000000], [735000000000]) (some (1, 2, 5)) (some (1, 2, 5))
    (.next ([-4302000000000], [4407000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.terminal (some
    (1, 2, 5)) (some (1, 2, 5)) (some (1, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan39Owner6Part0 : FanWitness := (.next ([1905000000000, -9000000000000], [4485000000000,
    9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1287000000000], [3963000000000])
    (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1500000000000], [4890000000000]) (some (5, 1, 6))
    (some (5, 1, 6)) (.next ([213000000000], [927000000000]) (some (5, 1, 6)) (some (5, 1, 6))
    (.next ([810000000000], [5625000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
    ([45000000000], [690000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([105000000000],
    [4302000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([0], [5355000000000]) (some (0, 1,
    6)) (some (0, 1, 6)) (.next ([-948000000000], [5250000000000]) (some (0, 1, 6)) (some (0, 2, 6))
    (.next ([-1035000000000], [4515000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-1080000000000], [3825000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-477000000000],
    [1662000000000]) (some (0, 2, 6)) (some (1, 2, 6)) (.next ([-1875000000000], [6390000000000])
    (some (1, 2, 6)) (some (1, 2, 6)) (.next ([-2610000000000, -9000000000000], [7965000000000,
    9000000000000]) (some (1, 2, 6)) (some (1, 2, 6)) (.next ([-3015000000000], [8370000000000])
    (some (1, 2, 6)) (some (1, 2, 6)) (.next ([-2610000000000], [6435000000000]) (some (1, 2, 6))
    (some (1, 2, 6)) (.next ([-3558000000000, -9000000000000], [5250000000000]) (some (1, 2, 6))
    (some (1, 2, 6)) (.next ([-4485000000000, -9000000000000], [6390000000000]) (some (1, 2, 6))
    (some (1, 2, 6)) (.next ([-3963000000000], [5250000000000]) (some (1, 2, 6)) (some (1, 2, 6))
    (.next ([-4890000000000], [6390000000000]) (some (1, 2, 4)) (some (1, 2, 4)) (.next
    ([-927000000000], [1140000000000]) (some (1, 2, 4)) (some (1, 2, 4)) (.next ([-5625000000000],
    [6435000000000]) (some (1, 2, 4)) (some (1, 2, 5)) (.next ([-690000000000], [735000000000])
    (some (1, 2, 5)) (some (1, 2, 5)) (.next ([-4302000000000], [4407000000000]) (some (1, 2, 5))
    (some (1, 2, 5)) (.terminal (some (1, 2, 5)) (some (1, 2, 5)) (some (1, 2,
    5)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_1 : ExcludedOn (model32.B 1 ++ [step32.q]) 9000000000000 (model32.caps 1)
    (model32.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_5 : ExcludedOn (model32.B 5 ++ [step32.q]) 9000000000000 (model32.caps 5)
    (model32.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2265000000000], [45000000000]) (some (4, 0, 2))
      (some (4, 1, 3)) (.next ([4320000000000], [2085000000000]) (some (4, 1, 3)) (some (4, 1, 5))
      (.next ([2610000000000], [1515000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([4320000000000, 0], [2610000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([3795000000000, -9000000000000], [2610000000000, 9000000000000]) (some (0, 1, 5)) (some (0,
      1, 5)) (.next ([2280000000000], [2610000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([2805000000000], [4125000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([2565000000000],
      [3825000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([495000000000], [6390000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([15000000000], [2565000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([0], [4320000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-45000000000], [2310000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-2085000000000],
      [6405000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1515000000000], [4125000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2610000000000, -9000000000000], [6930000000000,
      9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2610000000000, -9000000000000],
      [6405000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2610000000000], [4890000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4125000000000], [6930000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-3825000000000], [6390000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-6390000000000], [6885000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-2565000000000], [2580000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_1 : ExcludedOn (model33.B 1 ++ [step33.q]) 9000000000000 (model33.caps 1)
    (model33.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([1677000000000], [33000000000]) (some (6, 0, 4))
      (some (6, 7, 4)) (.next ([6195000000000], [165000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([3345000000000], [135000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([3600000000000], [150000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([255000000000],
      [15000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([5262000000000], [1113000000000])
      (some (6, 7, 4)) (some (6, 7, 4)) (.next ([3615000000000], [1083000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([3585000000000], [1080000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([3585000000000], [2760000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([1755000000000], [1995000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([1185000000000],
      [1440000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([3585000000000], [4605000000000])
      (some (6, 7, 4)) (some (6, 7, 4)) (.next ([1500000000000], [1980000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([2625000000000], [3480000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([2610000000000], [3750000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([1905000000000], [2760000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([1770000000000],
      [2928000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([915000000000], [1695000000000])
      (some (6, 7, 4)) (some (6, 7, 4)) (.next ([1677000000000], [4698000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([270000000000], [948000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([105000000000], [6105000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([15000000000], [933000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([60000000000],
      [4605000000000]) (some (6, 7, 4)) (some (6, 7, 4)) fan33Owner4Part0))))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded33_6
    · exact excluded33_7
    · exact excluded33_8
    · exact excluded33_9
theorem next33 : model33.insert step33 = model34 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded34_1 : ExcludedOn (model34.B 1 ++ [step34.q]) 9000000000000 (model34.caps 1)
    (model34.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_3 : ExcludedOn (model34.B 3 ++ [step34.q]) 9000000000000 (model34.caps 3)
    (model34.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7635000000000], [1365000000000]) (some (2, 4,
      4)) (some (3, 4, 4)) (.next ([6978000000000], [1647000000000]) (some (3, 4, 2)) (some (3, 4,
      2)) (.next ([4698000000000], [2235000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([4980000000000], [2610000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([282000000000], [375000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([2655000000000], [6345000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([375000000000],
      [4323000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0], [2610000000000,
      9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-1365000000000], [9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1647000000000], [8625000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-2235000000000, -9000000000000], [6933000000000, 9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2610000000000, -9000000000000], [7590000000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-375000000000], [657000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-6345000000000], [9000000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-4323000000000], [4698000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (4, 4, 2)) (some (4, 4, 2))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_4 : ExcludedOn (model34.B 4 ++ [step34.q]) 9000000000000 (model34.caps 4)
    (model34.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2595000000000], [15000000000]) (some (6, 0, 4))
      (some (6, 1, 4)) (.next ([1647000000000], [30000000000]) (some (6, 1, 4)) (some (6, 1, 4))
      (.next ([1677000000000], [33000000000]) (some (6, 1, 4)) (some (6, 1, 7)) (.next
      ([6195000000000], [165000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([3345000000000],
      [135000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([3600000000000], [150000000000])
      (some (6, 1, 7)) (some (6, 1, 7)) (.next ([255000000000], [15000000000]) (some (6, 1, 7))
      (some (6, 1, 7)) (.next ([5262000000000], [1113000000000]) (some (6, 1, 7)) (some (6, 1, 7))
      (.next ([3615000000000], [1083000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
      ([3585000000000], [1080000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([3585000000000],
      [2760000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([1185000000000], [1440000000000])
      (some (6, 1, 7)) (some (6, 1, 7)) (.next ([2625000000000], [3480000000000]) (some (6, 1, 7))
      (some (6, 1, 7)) (.next ([2610000000000], [3750000000000]) (some (6, 1, 7)) (some (6, 1, 7))
      (.next ([1905000000000], [2760000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
      ([915000000000], [1695000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([1677000000000],
      [4698000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([270000000000], [948000000000])
      (some (6, 1, 7)) (some (6, 1, 7)) (.next ([240000000000], [2625000000000]) (some (6, 1, 7))
      (some (6, 1, 7)) fan34Owner4Part0)))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2595000000000], [60000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([6345000000000], [2655000000000]) (some (5, 1, 2)) (some (5, 1, 3))
      (.next ([4395000000000], [2010000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([2610000000000], [1515000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4395000000000,
      0], [2610000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([3795000000000,
      -9000000000000], [2610000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([2280000000000], [2610000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2880000000000],
      [4125000000000]) (some (5, 1, 3)) (some (5, 1, 4)) (.next ([2220000000000], [5265000000000])
      (some (5, 1, 4)) (some (5, 1, 4)) (.next ([1740000000000], [4605000000000]) (some (5, 1, 4))
      (some (5, 1, 4)) (.next ([0], [4395000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-60000000000], [2655000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-2655000000000],
      [9000000000000]) (some (0, 2, 4)) (some (0, 2, 5)) (.next ([-2010000000000], [6405000000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1515000000000], [4125000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([-2610000000000, -9000000000000], [7005000000000, 9000000000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2610000000000, -9000000000000], [6405000000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2610000000000], [4890000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([-4125000000000], [7005000000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-5265000000000], [7485000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-4605000000000], [6345000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2,
      5)) (some (0, 2, 5)) (some (0, 2, 5))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_1 : ExcludedOn (model35.B 1 ++ [step35.q]) 9000000000000 (model35.caps 1)
    (model35.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_5 : ExcludedOn (model35.B 5 ++ [step35.q]) 9000000000000 (model35.caps 5)
    (model35.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1515000000000, -9000000000000], [0,
      9000000000000]) (some (4, 0, 2)) (some (4, 5, 2)) (.next ([6405000000000], [1650000000000])
      (some (4, 5, 2)) (some (4, 5, 3)) (.next ([4395000000000], [2010000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([2610000000000], [1515000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([4395000000000, 0], [2610000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([3795000000000, -9000000000000], [2610000000000, 9000000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([2280000000000], [2610000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([2880000000000], [4125000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next
      ([960000000000, 9000000000000], [1650000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([960000000000], [3165000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([0],
      [4395000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([0, -9000000000000],
      [1515000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-1650000000000], [8055000000000])
      (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2010000000000], [6405000000000]) (some (0, 5, 4))
      (some (0, 5, 4)) (.next ([-1515000000000], [4125000000000]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([-2610000000000, -9000000000000], [7005000000000, 9000000000000]) (some (0, 5, 4))
      (some (0, 5, 4)) (.next ([-2610000000000, -9000000000000], [6405000000000]) (some (0, 5, 4))
      (some (0, 5, 4)) (.next ([-2610000000000], [4890000000000]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([-4125000000000], [7005000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-1650000000000, 0], [2610000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-3165000000000], [4125000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_6 : ExcludedOn (model35.B 6 ++ [step35.q]) 9000000000000 (model35.caps 6)
    (model35.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded35_6
    · exact excluded35_7
    · exact excluded35_8
    · exact (hj rfl).elim
theorem next35 : model35.insert step35 = model36 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded36_0 : ExcludedOn (model36.B 0 ++ [step36.q]) 9000000000000 (model36.caps 0)
    (model36.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_1 : ExcludedOn (model36.B 1 ++ [step36.q]) 9000000000000 (model36.caps 1)
    (model36.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1515000000000, -9000000000000], [0,
      9000000000000]) (some (4, 0, 5)) (some (4, 1, 5)) (.next ([4395000000000], [2010000000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2610000000000], [1515000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([4395000000000, 0], [2610000000000, 9000000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([3795000000000, -9000000000000], [2610000000000, 9000000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([4395000000000], [3645000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([2280000000000], [2610000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([2760000000000], [3645000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([2880000000000], [4125000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([480000000000],
      [1035000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0], [4395000000000]) (some (0, 1,
      4)) (some (0, 1, 4)) (.next ([0, -9000000000000], [1515000000000]) (some (0, 1, 4)) (some (0,
      5, 4)) (.next ([-2010000000000], [6405000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-1515000000000], [4125000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2610000000000,
      -9000000000000], [7005000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-2610000000000, -9000000000000], [6405000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-3645000000000], [8040000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-2610000000000], [4890000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-3645000000000], [6405000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-4125000000000], [7005000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-1035000000000], [1515000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5,
      4)) (some (0, 5, 4)) (some (0, 5, 4))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([1995000000000], [1650000000000]) (some (3, 0,
      1)) (some (3, 1, 2)) (.next ([3750000000000], [3600000000000]) (some (0, 1, 2)) (some (0, 1,
      2)) (.next ([3645000000000], [5355000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([45000000000], [5355000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [7350000000000]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([-1650000000000], [3645000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3600000000000], [7350000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-5355000000000], [9000000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-5355000000000], [5400000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some
      (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6240000000000], [450000000000]) (some (4, 0, 5))
      (some (4, 0, 5)) (.next ([4995000000000], [435000000000]) (some (4, 0, 5)) (some (4, 0, 5))
      (.next ([2625000000000], [420000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
      ([3000000000000], [645000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([4770000000000],
      [1035000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([6570000000000], [2250000000000])
      (some (4, 0, 5)) (some (4, 0, 5)) fan37Owner0Part0))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_2 : ExcludedOn (model37.B 2 ++ [step37.q]) 9000000000000 (model37.caps 2)
    (model37.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2475000000000, -9000000000000], [360000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([6390000000000, -9000000000000],
      [2610000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2835000000000],
      [3915000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([225000000000, -9000000000000],
      [6525000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0, 0],
      [2610000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-360000000000,
      -9000000000000], [2835000000000, 0]) (some (0, 3, 1)) (some (0, 3, 2)) (.next
      ([-2610000000000, -9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-3915000000000], [6750000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-6525000000000, -9000000000000], [6750000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.terminal (some (0, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_3 : ExcludedOn (model37.B 3 ++ [step37.q]) 9000000000000 (model37.caps 3)
    (model37.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_4 : ExcludedOn (model37.B 4 ++ [step37.q]) 9000000000000 (model37.caps 4)
    (model37.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_5 : ExcludedOn (model37.B 5 ++ [step37.q]) 9000000000000 (model37.caps 5)
    (model37.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_6 : ExcludedOn (model37.B 6 ++ [step37.q]) 9000000000000 (model37.caps 6)
    (model37.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_7 : ExcludedOn (model37.B 7 ++ [step37.q]) 9000000000000 (model37.caps 7)
    (model37.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_8 : ExcludedOn (model37.B 8 ++ [step37.q]) 9000000000000 (model37.caps 8)
    (model37.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_9 : ExcludedOn (model37.B 9 ++ [step37.q]) 9000000000000 (model37.caps 9)
    (model37.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded38_0 : ExcludedOn (model38.B 0 ++ [step38.q]) 9000000000000 (model38.caps 0)
    (model38.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_2 : ExcludedOn (model38.B 2 ++ [step38.q]) 9000000000000 (model38.caps 2)
    (model38.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_3 : ExcludedOn (model38.B 3 ++ [step38.q]) 9000000000000 (model38.caps 3)
    (model38.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_4 : ExcludedOn (model38.B 4 ++ [step38.q]) 9000000000000 (model38.caps 4)
    (model38.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_5 : ExcludedOn (model38.B 5 ++ [step38.q]) 9000000000000 (model38.caps 5)
    (model38.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_6 : ExcludedOn (model38.B 6 ++ [step38.q]) 9000000000000 (model38.caps 6)
    (model38.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4695000000000], [165000000000]) (some (5, 1, 2))
      (some (5, 1, 3)) (.next ([4302000000000], [948000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([3480000000000], [1035000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([2745000000000], [1080000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1185000000000],
      [477000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4515000000000], [1875000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([5355000000000], [2610000000000, 9000000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([3825000000000], [2610000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([2250000000000], [1740000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([3615000000000], [3990000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([1692000000000, -9000000000000], [3558000000000, 9000000000000]) (some (5, 1, 3)) (some (5,
      1, 3)) fan38Owner6Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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

theorem excluded39_0 : ExcludedOn (model39.B 0 ++ [step39.q]) 9000000000000 (model39.caps 0)
    (model39.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_2 : ExcludedOn (model39.B 2 ++ [step39.q]) 9000000000000 (model39.caps 2)
    (model39.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_3 : ExcludedOn (model39.B 3 ++ [step39.q]) 9000000000000 (model39.caps 3)
    (model39.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_4 : ExcludedOn (model39.B 4 ++ [step39.q]) 9000000000000 (model39.caps 4)
    (model39.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_5 : ExcludedOn (model39.B 5 ++ [step39.q]) 9000000000000 (model39.caps 5)
    (model39.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_6 : ExcludedOn (model39.B 6 ++ [step39.q]) 9000000000000 (model39.caps 6)
    (model39.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4302000000000], [948000000000]) (some (5, 1, 2))
      (some (5, 1, 6)) (.next ([3480000000000], [1035000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([2745000000000], [1080000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([1185000000000], [477000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([4515000000000],
      [1875000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([5355000000000], [2610000000000,
      9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([5355000000000], [3015000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([3825000000000], [2610000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([1692000000000, -9000000000000], [3558000000000, 9000000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) fan39Owner6Part0)))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel)
      0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded39_2
    · exact excluded39_3
    · exact excluded39_4
    · exact excluded39_5
    · exact excluded39_6
    · exact excluded39_7
    · exact excluded39_8
    · exact excluded39_9
theorem next39 : model39.insert step39 = model40 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint290000300000
end ConwaySoifer.Simplified.Certificates
