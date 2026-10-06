/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint140000150000
import Mathlib.Tactic.FinCases

/-!
# Sint 140000 150000 7

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
namespace Sint140000150000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan56Owner0Part0 : FanWitness := (.next ([-1590000000000], [6750000000000]) (some (1, 4, 8))
    (some (1, 4, 8)) (.next ([-480000000000], [2010000000000]) (some (1, 4, 8)) (some (1, 4, 8))
    (.next ([-1680000000000], [6750000000000]) (some (1, 4, 8)) (some (1, 4, 8)) (.next
    ([-1590000000000], [5925000000000]) (some (1, 4, 8)) (some (1, 4, 8)) (.next ([-1680000000000],
    [5925000000000]) (some (1, 4, 8)) (some (1, 4, 8)) (.next ([-810000000000], [2730000000000])
    (some (1, 4, 8)) (some (1, 4, 8)) (.next ([-2010000000000], [6420000000000]) (some (1, 4, 6))
    (some (1, 4, 6)) (.next ([-390000000000], [1140000000000]) (some (1, 4, 6)) (some (1, 4, 6))
    (.next ([-2010000000000], [5595000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next
    ([-480000000000], [1230000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-330000000000],
    [750000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-1305000000000], [2835000000000])
    (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-420000000000], [840000000000]) (some (1, 4, 6))
    (some (1, 4, 6)) (.next ([-4560000000000], [8370000000000]) (some (1, 4, 6)) (some (1, 5, 6))
    (.next ([-4890000000000], [8310000000000]) (some (1, 5, 6)) (some (1, 5, 6)) (.next
    ([-2820000000000], [4260000000000]) (some (1, 5, 6)) (some (1, 5, 6)) (.next ([-5310000000000],
    [7980000000000]) (some (1, 5, 6)) (some (1, 5, 6)) (.next ([-5310000000000], [7890000000000])
    (some (1, 5, 6)) (some (1, 5, 6)) (.next ([-4980000000000], [7230000000000]) (some (1, 5, 6))
    (some (1, 5, 6)) (.next ([-1140000000000], [1560000000000]) (some (1, 5, 6)) (some (1, 8, 6))
    (.next ([-3645000000000], [4260000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next
    ([-6480000000000], [7560000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-6810000000000],
    [7500000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-1080000000000], [1170000000000])
    (some (1, 8, 6)) (some (1, 8, 6)) (.terminal (some (1, 8, 6)) (some (1, 8, 6)) (some (1, 8,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan56Owner0Part1 : FanWitness := (.next ([750000000000], [480000000000]) (some (7, 2, 8)) (some
    (7, 2, 8)) (.next ([420000000000], [330000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
    ([1530000000000], [1305000000000]) (some (7, 2, 8)) (some (7, 3, 8)) (.next ([420000000000],
    [420000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([3810000000000], [4560000000000])
    (some (7, 3, 8)) (some (7, 3, 8)) (.next ([3420000000000], [4890000000000]) (some (7, 3, 8))
    (some (7, 3, 8)) (.next ([1440000000000], [2820000000000]) (some (7, 3, 8)) (some (7, 3, 8))
    (.next ([2670000000000], [5310000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next
    ([2580000000000], [5310000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([2250000000000],
    [4980000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([420000000000], [1140000000000])
    (some (7, 3, 8)) (some (7, 3, 8)) (.next ([615000000000], [3645000000000]) (some (7, 3, 8))
    (some (7, 3, 8)) (.next ([1080000000000], [6480000000000]) (some (7, 3, 8)) (some (7, 3, 8))
    (.next ([690000000000], [6810000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next
    ([90000000000], [1080000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([0], [825000000000])
    (some (7, 3, 8)) (some (7, 3, 8)) (.next ([-60000000000], [7230000000000]) (some (0, 3, 8))
    (some (0, 4, 8)) (.next ([-150000000000], [7230000000000]) (some (0, 4, 8)) (some (0, 4, 8))
    (.next ([-480000000000], [6900000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next
    ([-450000000000], [6000000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next ([-450000000000],
    [5175000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next ([-840000000000], [6330000000000])
    (some (0, 4, 8)) (some (1, 4, 8)) (.next ([-840000000000], [5505000000000]) (some (1, 4, 8))
    (some (1, 4, 8)) (.next ([-60000000000], [390000000000]) (some (1, 4, 8)) (some (1, 4, 8))
    fan56Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan58Owner5Part0 : FanWitness := (.next ([6000000000000, 0], [1260000000000, 9000000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([2235000000000, -9000000000000], [630000000000]) (some
    (0, 1, 5)) (some (0, 1, 5)) (.next ([5580000000000], [1875000000000]) (some (0, 1, 5)) (some (0,
    1, 5)) (.next ([3780000000000, -9000000000000], [1470000000000, 9000000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([5370000000000], [4125000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([2250000000000], [3960000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([960000000000], [2790000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([915000000000],
    [3705000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([990000000000, -9000000000000],
    [5220000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([750000000000],
    [5040000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0], [6000000000000]) (some (0, 1,
    3)) (some (0, 1, 3)) (.next ([-210000000000], [5250000000000]) (some (0, 1, 3)) (some (0, 2, 3))
    (.next ([-210000000000], [2250000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([-630000000000], [4125000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1260000000000,
    -9000000000000], [7260000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([-630000000000, 0], [2865000000000, -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([-1875000000000], [7455000000000]) (some (0, 2, 3)) (some (0, 5, 3)) (.next ([-1470000000000,
    -9000000000000], [5250000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4125000000000],
    [9495000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3960000000000], [6210000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2790000000000], [3750000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-3705000000000], [4620000000000]) (some (0, 5, 3)) (some (0, 5, 4))
    (.next ([-5220000000000, -9000000000000], [6210000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-5040000000000], [5790000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some
    (0, 5, 4)) (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

theorem excluded56_0 : ExcludedOn (model56.B 0 ++ [step56.q]) 9000000000000 (model56.caps 0)
    (model56.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7170000000000], [60000000000]) (some (6, 1, 8))
      (some (6, 1, 8)) (.next ([7080000000000], [150000000000]) (some (6, 1, 8)) (some (6, 1, 8))
      (.next ([6420000000000], [480000000000]) (some (6, 1, 8)) (some (6, 1, 8)) (.next
      ([5550000000000], [450000000000]) (some (6, 1, 8)) (some (6, 1, 8)) (.next ([4725000000000],
      [450000000000]) (some (6, 1, 8)) (some (6, 1, 8)) (.next ([5490000000000], [840000000000])
      (some (6, 1, 8)) (some (6, 1, 8)) (.next ([4665000000000], [840000000000]) (some (6, 1, 8))
      (some (6, 1, 8)) (.next ([330000000000], [60000000000]) (some (6, 1, 8)) (some (6, 1, 8))
      (.next ([5160000000000], [1590000000000]) (some (6, 1, 8)) (some (6, 2, 8)) (.next
      ([1530000000000], [480000000000]) (some (6, 2, 8)) (some (6, 2, 8)) (.next ([5070000000000],
      [1680000000000]) (some (6, 2, 8)) (some (7, 2, 8)) (.next ([4335000000000], [1590000000000])
      (some (7, 2, 8)) (some (7, 2, 8)) (.next ([4245000000000], [1680000000000]) (some (7, 2, 8))
      (some (7, 2, 8)) (.next ([1920000000000], [810000000000]) (some (7, 2, 8)) (some (7, 2, 8))
      (.next ([4410000000000], [2010000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
      ([750000000000], [390000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([3585000000000],
      [2010000000000]) (some (7, 2, 8)) (some (7, 2, 8)) fan56Owner0Part1)))))))))))))))))) (den :=
      9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded56_2 : ExcludedOn (model56.B 2 ++ [step56.q]) 9000000000000 (model56.caps 2)
    (model56.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7740000000000, -9000000000000], [1260000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([3300000000000, -9000000000000],
      [1440000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1440000000000],
      [3000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([180000000000, -9000000000000],
      [4260000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0],
      [1260000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-1260000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next
      ([-1440000000000, 0], [4740000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-3000000000000], [4440000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-4260000000000, -9000000000000], [4440000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.terminal (some (0, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded56_3 : ExcludedOn (model56.B 3 ++ [step56.q]) 9000000000000 (model56.caps 3)
    (model56.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_4 : ExcludedOn (model56.B 4 ++ [step56.q]) 9000000000000 (model56.caps 4)
    (model56.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_5 : ExcludedOn (model56.B 5 ++ [step56.q]) 9000000000000 (model56.caps 5)
    (model56.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_6 : ExcludedOn (model56.B 6 ++ [step56.q]) 9000000000000 (model56.caps 6)
    (model56.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_7 : ExcludedOn (model56.B 7 ++ [step56.q]) 9000000000000 (model56.caps 7)
    (model56.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_8 : ExcludedOn (model56.B 8 ++ [step56.q]) 9000000000000 (model56.caps 8)
    (model56.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_9 : ExcludedOn (model56.B 9 ++ [step56.q]) 9000000000000 (model56.caps 9)
    (model56.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked56 : StepValid model56 9000000000000 step56 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded56_0
    · exact (hj rfl).elim
    · exact excluded56_2
    · exact excluded56_3
    · exact excluded56_4
    · exact excluded56_5
    · exact excluded56_6
    · exact excluded56_7
    · exact excluded56_8
    · exact excluded56_9
theorem next56 : model56.insert step56 = model57 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded57_0 : ExcludedOn (model57.B 0 ++ [step57.q]) 9000000000000 (model57.caps 0)
    (model57.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_1 : ExcludedOn (model57.B 1 ++ [step57.q]) 9000000000000 (model57.caps 1)
    (model57.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_2 : ExcludedOn (model57.B 2 ++ [step57.q]) 9000000000000 (model57.caps 2)
    (model57.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_3 : ExcludedOn (model57.B 3 ++ [step57.q]) 9000000000000 (model57.caps 3)
    (model57.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_4 : ExcludedOn (model57.B 4 ++ [step57.q]) 9000000000000 (model57.caps 4)
    (model57.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_5 : ExcludedOn (model57.B 5 ++ [step57.q]) 9000000000000 (model57.caps 5)
    (model57.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5040000000000], [210000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) (.next ([2040000000000], [210000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([6210000000000], [1245000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([6000000000000, 0], [1260000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([3780000000000, -9000000000000], [1470000000000, 9000000000000]) (some (0, 1, 5)) (some (0,
      1, 5)) (.next ([6000000000000], [3495000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([2250000000000], [3960000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([1545000000000],
      [3705000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([960000000000], [2790000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([990000000000, -9000000000000], [5220000000000,
      9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([750000000000], [5040000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0], [6000000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([-210000000000], [5250000000000]) (some (0, 1, 3)) (some (0, 5, 3)) (.next
      ([-210000000000], [2250000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1245000000000],
      [7455000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1260000000000, -9000000000000],
      [7260000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1470000000000,
      -9000000000000], [5250000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3495000000000],
      [9495000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3960000000000], [6210000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3705000000000], [5250000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-2790000000000], [3750000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-5220000000000, -9000000000000], [6210000000000]) (some (0, 5, 3)) (some (0, 5, 4))
      (.next ([-5040000000000], [5790000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some
      (0, 5, 4)) (some (0, 5, 4)) (some (0, 5, 4))))))))))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded57_7 : ExcludedOn (model57.B 7 ++ [step57.q]) 9000000000000 (model57.caps 7)
    (model57.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_8 : ExcludedOn (model57.B 8 ++ [step57.q]) 9000000000000 (model57.caps 8)
    (model57.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_9 : ExcludedOn (model57.B 9 ++ [step57.q]) 9000000000000 (model57.caps 9)
    (model57.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5205000000000], [300000000000]) (some (3, 0, 1))
      (some (3, 1, 2)) (.next ([3495000000000], [210000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([3495000000000], [5505000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([1500000000000], [3795000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [5295000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-300000000000], [5505000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-210000000000], [3705000000000]) (some (3, 1, 2))
      (some (3, 1, 3)) (.next ([-5505000000000], [9000000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-3795000000000], [5295000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some
      (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem checked57 : StepValid model57 9000000000000 step57 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded57_0
    · exact excluded57_1
    · exact excluded57_2
    · exact excluded57_3
    · exact excluded57_4
    · exact excluded57_5
    · exact (hj rfl).elim
    · exact excluded57_7
    · exact excluded57_8
    · exact excluded57_9
theorem next57 : model57.insert step57 = model58 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded58_0 : ExcludedOn (model58.B 0 ++ [step58.q]) 9000000000000 (model58.caps 0)
    (model58.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_1 : ExcludedOn (model58.B 1 ++ [step58.q]) 9000000000000 (model58.caps 1)
    (model58.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_2 : ExcludedOn (model58.B 2 ++ [step58.q]) 9000000000000 (model58.caps 2)
    (model58.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_3 : ExcludedOn (model58.B 3 ++ [step58.q]) 9000000000000 (model58.caps 3)
    (model58.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_4 : ExcludedOn (model58.B 4 ++ [step58.q]) 9000000000000 (model58.caps 4)
    (model58.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_5 : ExcludedOn (model58.B 5 ++ [step58.q]) 9000000000000 (model58.caps 5)
    (model58.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5040000000000], [210000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) (.next ([2040000000000], [210000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([3495000000000], [630000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      fan58Owner5Part0)))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded58_7 : ExcludedOn (model58.B 7 ++ [step58.q]) 9000000000000 (model58.caps 7)
    (model58.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_8 : ExcludedOn (model58.B 8 ++ [step58.q]) 9000000000000 (model58.caps 8)
    (model58.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_9 : ExcludedOn (model58.B 9 ++ [step58.q]) 9000000000000 (model58.caps 9)
    (model58.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000], [210000000000]) (some (3, 0, 1))
      (some (3, 1, 2)) (.next ([4125000000000], [5505000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([1500000000000], [3795000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([330000000000], [5505000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [5295000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-210000000000], [4335000000000])
      (some (3, 1, 3)) (some (3, 1, 3)) (.next ([-5505000000000], [9630000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-3795000000000], [5295000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-5505000000000], [5835000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some
      (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem checked58 : StepValid model58 9000000000000 step58 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded58_0
    · exact excluded58_1
    · exact excluded58_2
    · exact excluded58_3
    · exact excluded58_4
    · exact excluded58_5
    · exact (hj rfl).elim
    · exact excluded58_7
    · exact excluded58_8
    · exact excluded58_9
theorem next58 : model58.insert step58 = model59 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded59_0 : ExcludedOn (model59.B 0 ++ [step59.q]) 9000000000000 (model59.caps 0)
    (model59.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_2 : ExcludedOn (model59.B 2 ++ [step59.q]) 9000000000000 (model59.caps 2)
    (model59.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_3 : ExcludedOn (model59.B 3 ++ [step59.q]) 9000000000000 (model59.caps 3)
    (model59.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_4 : ExcludedOn (model59.B 4 ++ [step59.q]) 9000000000000 (model59.caps 4)
    (model59.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_5 : ExcludedOn (model59.B 5 ++ [step59.q]) 9000000000000 (model59.caps 5)
    (model59.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_6 : ExcludedOn (model59.B 6 ++ [step59.q]) 9000000000000 (model59.caps 6)
    (model59.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5505000000000], [630000000000, 9000000000000])
      (some (5, 0, 1)) (some (5, 0, 5)) (.next ([4710000000000], [720000000000]) (some (5, 0, 5))
      (some (5, 0, 5)) (.next ([3960000000000], [750000000000]) (some (3, 0, 5)) (some (3, 0, 5))
      (.next ([5505000000000], [1260000000000, 9000000000000]) (some (3, 0, 5)) (some (3, 0, 5))
      (.next ([5505000000000], [4050000000000]) (some (3, 0, 5)) (some (3, 0, 5)) (.next
      ([2700000000000, -9000000000000], [2010000000000, 9000000000000]) (some (3, 0, 5)) (some (3,
      0, 5)) (.next ([5505000000000], [4680000000000]) (some (3, 0, 5)) (some (3, 0, 5)) (.next
      ([795000000000], [3330000000000]) (some (3, 0, 5)) (some (3, 0, 5)) (.next ([795000000000],
      [3960000000000]) (some (3, 0, 5)) (some (4, 0, 5)) (.next ([630000000000], [4875000000000])
      (some (4, 0, 5)) (some (4, 0, 5)) (.next ([0], [5505000000000]) (some (4, 0, 5)) (some (4, 0,
      5)) (.next ([-630000000000, -9000000000000], [6135000000000, 9000000000000]) (some (0, 0, 5))
      (some (0, 1, 5)) (.next ([-720000000000], [5430000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([-750000000000], [4710000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-1260000000000, -9000000000000], [6765000000000, 9000000000000]) (some (0, 1, 5)) (some (0,
      1, 5)) (.next ([-4050000000000], [9555000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-2010000000000, -9000000000000], [4710000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-4680000000000], [10185000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-3330000000000], [4125000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-3960000000000], [4755000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-4875000000000], [5505000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.terminal (some (0, 1,
      5)) (some (0, 1, 5)) (some (0, 1, 5))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded59_7 : ExcludedOn (model59.B 7 ++ [step59.q]) 9000000000000 (model59.caps 7)
    (model59.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_8 : ExcludedOn (model59.B 8 ++ [step59.q]) 9000000000000 (model59.caps 8)
    (model59.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_9 : ExcludedOn (model59.B 9 ++ [step59.q]) 9000000000000 (model59.caps 9)
    (model59.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked59 : StepValid model59 9000000000000 step59 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded59_0
    · exact (hj rfl).elim
    · exact excluded59_2
    · exact excluded59_3
    · exact excluded59_4
    · exact excluded59_5
    · exact excluded59_6
    · exact excluded59_7
    · exact excluded59_8
    · exact excluded59_9
theorem next59 : model59.insert step59 = model60 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint140000150000
end ConwaySoifer.Simplified.Certificates
