/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint170000180000
import Mathlib.Tactic.FinCases

/-!
# Sint 170000 180000 5

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
namespace Sint170000180000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan41Owner0Part0 : FanWitness := (.next ([-510000000000], [6630000000000]) (some (7, 3, 6))
    (some (7, 3, 6)) (.next ([-705000000000], [6885000000000]) (some (7, 3, 6)) (some (7, 3, 6))
    (.next ([-630000000000], [4890000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next
    ([-1020000000000], [5655000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-390000000000],
    [2025000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-840000000000], [2745000000000])
    (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-1905000000000], [6165000000000]) (some (7, 3, 6))
    (some (7, 3, 6)) (.next ([-1095000000000], [2805000000000]) (some (7, 3, 6)) (some (7, 3, 6))
    (.next ([-2415000000000], [5790000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next
    ([-375000000000], [885000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-885000000000],
    [1785000000000]) (some (7, 3, 6)) (some (7, 4, 6)) (.next ([-390000000000], [765000000000])
    (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-6120000000000], [9030000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-2025000000000], [2910000000000]) (some (7, 4, 6)) (some (7, 4, 6))
    (.next ([-6375000000000], [9090000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-195000000000], [255000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-1650000000000],
    [2025000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5730000000000], [7005000000000])
    (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5280000000000], [6285000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-5985000000000], [7065000000000]) (some (7, 4, 6)) (some (7, 4, 6))
    (.next ([-2910000000000], [3420000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-6495000000000], [7380000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-1260000000000],
    [1395000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-6750000000000], [7440000000000])
    (some (7, 4, 6)) (some (7, 4, 6)) (.terminal (some (7, 4, 6)) (some (7, 4, 6)) (some (7, 4,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan41Owner0Part1 : FanWitness := (.next ([4260000000000], [630000000000]) (some (6, 7, 5)) (some
    (6, 7, 5)) (.next ([4635000000000], [1020000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next
    ([1635000000000], [390000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next ([1905000000000],
    [840000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next ([4260000000000], [1905000000000])
    (some (6, 7, 5)) (some (6, 7, 5)) (.next ([1710000000000], [1095000000000]) (some (6, 7, 5))
    (some (6, 7, 5)) (.next ([3375000000000], [2415000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([510000000000], [375000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([900000000000], [885000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([375000000000],
    [390000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([2910000000000], [6120000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([885000000000], [2025000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([2715000000000], [6375000000000]) (some (0, 3, 5)) (some (0, 3, 5))
    (.next ([60000000000], [195000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([375000000000],
    [1650000000000]) (some (0, 3, 5)) (some (0, 3, 6)) (.next ([1275000000000], [5730000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([1005000000000], [5280000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([1080000000000], [5985000000000]) (some (0, 3, 6)) (some (7, 3, 6))
    (.next ([510000000000], [2910000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next
    ([885000000000], [6495000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([135000000000],
    [1260000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([690000000000], [6750000000000])
    (some (7, 3, 6)) (some (7, 3, 6)) (.next ([0], [1275000000000]) (some (7, 3, 6)) (some (7, 3,
    6)) (.next ([-195000000000], [7260000000000]) (some (7, 3, 6)) (some (7, 3, 6))
    fan41Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan43Owner5Part0 : FanWitness := (.next ([3360000000000], [510000000000]) (some (5, 1, 2)) (some
    (5, 1, 2)) (.next ([5460000000000, 0], [1530000000000, 9000000000000]) (some (5, 1, 2)) (some
    (5, 1, 2)) (.next ([6570000000000, -9000000000000], [2550000000000, 9000000000000]) (some (5, 1,
    2)) (some (5, 1, 2)) (.next ([3210000000000, -9000000000000], [2040000000000, 9000000000000])
    (some (5, 1, 2)) (some (5, 1, 5)) (.next ([4440000000000], [3660000000000]) (some (5, 1, 5))
    (some (5, 1, 5)) (.next ([3060000000000], [2524500000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([1504500000000], [3535500000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([1530000000000, -9000000000000], [4054500000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1,
    5)) (.next ([334500000000], [1680000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([210000000000], [4740000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0],
    [5460000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-124500000000], [3060000000000])
    (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-510000000000], [5250000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-1020000000000], [9120000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-510000000000], [3870000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1530000000000, -9000000000000], [6990000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2,
    5)) (.next ([-2550000000000, -9000000000000], [9120000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-2040000000000, -9000000000000], [5250000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-3660000000000], [8100000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-2524500000000], [5584500000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3535500000000],
    [5040000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4054500000000, -9000000000000],
    [5584500000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1680000000000], [2014500000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4740000000000], [4950000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan44Owner5Part0 : FanWitness := (.next ([4834500000000], [1350000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([5460000000000, 0], [1530000000000, 9000000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([2130000000000, -9000000000000], [750000000000]) (some (0, 1, 5)) (some
    (0, 1, 5)) (.next ([3210000000000, -9000000000000], [2040000000000, 9000000000000]) (some (0, 1,
    5)) (some (0, 1, 5)) (.next ([3060000000000], [2524500000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([4710000000000], [4410000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([1530000000000, -9000000000000], [4054500000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1,
    5)) (.next ([334500000000], [1680000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([330000000000], [4170000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([210000000000],
    [4740000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0], [5460000000000]) (some (0, 1,
    3)) (some (0, 1, 3)) (.next ([-124500000000], [3060000000000]) (some (0, 1, 3)) (some (0, 2, 3))
    (.next ([-510000000000], [5250000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([-750000000000], [4410000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1350000000000],
    [6184500000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1530000000000, -9000000000000],
    [6990000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-750000000000, 0],
    [2880000000000, -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2040000000000,
    -9000000000000], [5250000000000]) (some (0, 2, 3)) (some (0, 5, 3)) (.next ([-2524500000000],
    [5584500000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4410000000000], [9120000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4054500000000, -9000000000000], [5584500000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1680000000000], [2014500000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-4170000000000], [4500000000000]) (some (0, 5, 3)) (some (0, 5, 4))
    (.next ([-4740000000000], [4950000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some
    (0, 5, 4)) (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan45Owner5Part0 : FanWitness := (.next ([3210000000000, -9000000000000], [2040000000000,
    9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([3060000000000], [2524500000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([3660000000000], [4590000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([2130000000000, -9000000000000], [4590000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([1530000000000, -9000000000000], [4054500000000, 9000000000000]) (some
    (0, 1, 5)) (some (0, 1, 5)) (.next ([334500000000], [1680000000000]) (some (0, 1, 5)) (some (0,
    1, 5)) (.next ([994500000000], [5190000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([660000000000], [3510000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([870000000000],
    [8250000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([210000000000], [4740000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0], [5460000000000]) (some (0, 1, 5)) (some (0, 1,
    5)) (.next ([-124500000000], [3060000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
    ([-510000000000], [5250000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1530000000000,
    -9000000000000], [6990000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-2040000000000, -9000000000000], [5250000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-2524500000000], [5584500000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4590000000000],
    [8250000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4590000000000, 0], [6720000000000,
    -9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4054500000000, -9000000000000],
    [5584500000000]) (some (0, 2, 5)) (some (0, 5, 5)) (.next ([-1680000000000], [2014500000000])
    (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-5190000000000], [6184500000000]) (some (0, 5, 5))
    (some (0, 5, 5)) (.next ([-3510000000000], [4170000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-8250000000000], [9120000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-4740000000000], [4950000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5,
    4)) (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

theorem excluded40_0 : ExcludedOn (model40.B 0 ++ [step40.q]) 9000000000000 (model40.caps 0)
    (model40.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_1 : ExcludedOn (model40.B 1 ++ [step40.q]) 9000000000000 (model40.caps 1)
    (model40.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_2 : ExcludedOn (model40.B 2 ++ [step40.q]) 9000000000000 (model40.caps 2)
    (model40.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_3 : ExcludedOn (model40.B 3 ++ [step40.q]) 9000000000000 (model40.caps 3)
    (model40.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_4 : ExcludedOn (model40.B 4 ++ [step40.q]) 9000000000000 (model40.caps 4)
    (model40.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2625000000000, -9000000000000], [0,
      9000000000000]) (some (4, 0, 3)) (some (4, 5, 3)) (.next ([5121000000000], [474000000000])
      (some (4, 5, 3)) (some (4, 5, 3)) (.next ([5121000000000, 0], [1530000000000, 9000000000000])
      (some (4, 5, 3)) (some (4, 5, 3)) (.next ([4065000000000, -9000000000000], [1530000000000,
      9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([5121000000000], [3540000000000])
      (some (4, 5, 3)) (some (4, 5, 3)) (.next ([1440000000000], [1530000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([2496000000000], [4155000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([1530000000000], [2625000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([2055000000000], [3540000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([615000000000],
      [2010000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0, 0], [1530000000000,
      9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0, -9000000000000], [2625000000000,
      0]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-474000000000], [5595000000000]) (some (0, 5,
      3)) (some (0, 5, 3)) (.next ([-1530000000000, -9000000000000], [6651000000000, 9000000000000])
      (some (0, 5, 3)) (some (0, 5, 4)) (.next ([-1530000000000, -9000000000000], [5595000000000,
      0]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3540000000000], [8661000000000]) (some (0, 5,
      4)) (some (0, 5, 4)) (.next ([-1530000000000], [2970000000000]) (some (0, 5, 4)) (some (0, 5,
      4)) (.next ([-4155000000000], [6651000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-2625000000000], [4155000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-3540000000000], [5595000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-2010000000000], [2625000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.terminal (some (0, 3,
      4)) (some (0, 3, 4)) (some (0, 3, 4))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_6 : ExcludedOn (model40.B 6 ++ [step40.q]) 9000000000000 (model40.caps 6)
    (model40.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_7 : ExcludedOn (model40.B 7 ++ [step40.q]) 9000000000000 (model40.caps 7)
    (model40.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_8 : ExcludedOn (model40.B 8 ++ [step40.q]) 9000000000000 (model40.caps 8)
    (model40.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_9 : ExcludedOn (model40.B 9 ++ [step40.q]) 9000000000000 (model40.caps 9)
    (model40.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked40 : StepValid model40 9000000000000 step40 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded40_0
    · exact excluded40_1
    · exact excluded40_2
    · exact excluded40_3
    · exact excluded40_4
    · exact (hj rfl).elim
    · exact excluded40_6
    · exact excluded40_7
    · exact excluded40_8
    · exact excluded40_9
theorem next40 : model40.insert step40 = model41 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded41_0 : ExcludedOn (model41.B 0 ++ [step41.q]) 9000000000000 (model41.caps 0)
    (model41.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7065000000000], [195000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([6120000000000], [510000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([6180000000000], [705000000000]) (some (6, 7, 4)) (some (6, 7, 5))
      fan41Owner0Part1))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded41_1 : ExcludedOn (model41.B 1 ++ [step41.q]) 9000000000000 (model41.caps 1)
    (model41.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_2 : ExcludedOn (model41.B 2 ++ [step41.q]) 9000000000000 (model41.caps 2)
    (model41.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_3 : ExcludedOn (model41.B 3 ++ [step41.q]) 9000000000000 (model41.caps 3)
    (model41.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8880000000000], [120000000000]) (some (3, 5, 5))
      (some (4, 5, 5)) (.next ([8535000000000], [219000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([480000000000, -9000000000000], [30000000000, 9000000000000]) (some (4, 5, 3)) (some
      (4, 5, 3)) (.next ([1500000000000], [510000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([5835000000000], [2010000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([99000000000],
      [246000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([2535000000000], [6465000000000])
      (some (4, 5, 3)) (some (4, 5, 3)) (.next ([1035000000000], [5955000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([1005000000000, -9000000000000], [6465000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([246000000000], [6000000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([0], [1530000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([-120000000000], [9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-219000000000],
      [8754000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-30000000000, -9000000000000],
      [510000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-510000000000], [2010000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2010000000000], [7845000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-246000000000], [345000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-6465000000000], [9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-5955000000000], [6990000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-6465000000000], [7470000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-6000000000000], [6246000000000]) (some (0, 5, 3)) (some (5, 5, 3)) (.terminal (some (5, 5,
      3)) (some (5, 5, 3)) (some (5, 5, 3))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded41_5 : ExcludedOn (model41.B 5 ++ [step41.q]) 9000000000000 (model41.caps 5)
    (model41.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4740000000000], [510000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([5460000000000, 0], [1530000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([6465000000000], [2535000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([3210000000000, -9000000000000], [2040000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([4935000000000, -9000000000000], [4065000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 3)) (.next ([1725000000000], [2025000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([2925000000000], [3540000000000]) (some (4, 1, 3)) (some (4, 1, 4))
      (.next ([210000000000], [4740000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [5460000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-510000000000], [5250000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1530000000000, -9000000000000], [6990000000000,
      9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2535000000000], [9000000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2040000000000, -9000000000000], [5250000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4065000000000, -9000000000000], [9000000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2025000000000], [3750000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-3540000000000], [6465000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-4740000000000], [4950000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded41_6 : ExcludedOn (model41.B 6 ++ [step41.q]) 9000000000000 (model41.caps 6)
    (model41.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_7 : ExcludedOn (model41.B 7 ++ [step41.q]) 9000000000000 (model41.caps 7)
    (model41.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_8 : ExcludedOn (model41.B 8 ++ [step41.q]) 9000000000000 (model41.caps 8)
    (model41.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_9 : ExcludedOn (model41.B 9 ++ [step41.q]) 9000000000000 (model41.caps 9)
    (model41.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked41 : StepValid model41 9000000000000 step41 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded41_0
    · exact excluded41_1
    · exact excluded41_2
    · exact excluded41_3
    · exact (hj rfl).elim
    · exact excluded41_5
    · exact excluded41_6
    · exact excluded41_7
    · exact excluded41_8
    · exact excluded41_9
theorem next41 : model41.insert step41 = model42 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded42_0 : ExcludedOn (model42.B 0 ++ [step42.q]) 9000000000000 (model42.caps 0)
    (model42.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_1 : ExcludedOn (model42.B 1 ++ [step42.q]) 9000000000000 (model42.caps 1)
    (model42.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_2 : ExcludedOn (model42.B 2 ++ [step42.q]) 9000000000000 (model42.caps 2)
    (model42.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_3 : ExcludedOn (model42.B 3 ++ [step42.q]) 9000000000000 (model42.caps 3)
    (model42.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_4 : ExcludedOn (model42.B 4 ++ [step42.q]) 9000000000000 (model42.caps 4)
    (model42.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3405000000000], [10500000000]) (some (4, 0, 5))
      (some (4, 1, 5)) (.next ([1885500000000], [435000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([5121000000000], [1344000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([5121000000000, 0], [1530000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([4935000000000, -9000000000000], [1530000000000, 9000000000000]) (some (4, 1, 3)) (some (4,
      1, 3)) (.next ([2310000000000], [1530000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([3415500000000], [3060000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1885500000000,
      -9000000000000], [3060000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([1530000000000], [2625000000000]) (some (4, 1, 3)) (some (4, 5, 3)) (.next ([2061000000000],
      [6475500000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0, 0], [1530000000000,
      9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([-10500000000], [3415500000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-435000000000], [2320500000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-1344000000000], [6465000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-1530000000000, -9000000000000], [6651000000000, 9000000000000]) (some (0, 5, 3))
      (some (0, 5, 4)) (.next ([-1530000000000, -9000000000000], [6465000000000, 0]) (some (0, 5,
      4)) (some (0, 5, 4)) (.next ([-1530000000000], [3840000000000]) (some (0, 5, 4)) (some (0, 5,
      4)) (.next ([-3060000000000], [6475500000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-3060000000000, 0], [4945500000000, -9000000000000]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([-2625000000000], [4155000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-6475500000000], [8536500000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5,
      4)) (some (0, 5, 4)) (some (0, 5, 4))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded42_6 : ExcludedOn (model42.B 6 ++ [step42.q]) 9000000000000 (model42.caps 6)
    (model42.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_7 : ExcludedOn (model42.B 7 ++ [step42.q]) 9000000000000 (model42.caps 7)
    (model42.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_8 : ExcludedOn (model42.B 8 ++ [step42.q]) 9000000000000 (model42.caps 8)
    (model42.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_9 : ExcludedOn (model42.B 9 ++ [step42.q]) 9000000000000 (model42.caps 9)
    (model42.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked42 : StepValid model42 9000000000000 step42 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded42_0
    · exact excluded42_1
    · exact excluded42_2
    · exact excluded42_3
    · exact excluded42_4
    · exact (hj rfl).elim
    · exact excluded42_6
    · exact excluded42_7
    · exact excluded42_8
    · exact excluded42_9
theorem next42 : model42.insert step42 = model43 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded43_1 : ExcludedOn (model43.B 1 ++ [step43.q]) 9000000000000 (model43.caps 1)
    (model43.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_2 : ExcludedOn (model43.B 2 ++ [step43.q]) 9000000000000 (model43.caps 2)
    (model43.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_3 : ExcludedOn (model43.B 3 ++ [step43.q]) 9000000000000 (model43.caps 3)
    (model43.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6870000000000], [600000000000]) (some (3, 0, 5))
      (some (4, 0, 5)) (.next ([6246000000000], [1284000000000, 9000000000000]) (some (4, 0, 5))
      (some (4, 5, 5)) (.next ([7245000000000], [1635000000000]) (some (4, 5, 5)) (some (4, 5, 5))
      (.next ([6345000000000], [1530000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([5736000000000], [1764000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([1500000000000], [510000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([5835000000000],
      [2010000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([99000000000], [246000000000])
      (some (4, 5, 3)) (some (4, 5, 3)) (.next ([900000000000], [7980000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([246000000000], [6000000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([0], [1530000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([-600000000000], [7470000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1284000000000,
      -9000000000000], [7530000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-1635000000000], [8880000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1530000000000,
      -9000000000000], [7875000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-1764000000000], [7500000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-510000000000],
      [2010000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2010000000000], [7845000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-246000000000], [345000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-7980000000000], [8880000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-6000000000000], [6246000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some
      (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3))))))))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded43_4 : ExcludedOn (model43.B 4 ++ [step43.q]) 9000000000000 (model43.caps 4)
    (model43.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7980000000000], [120000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) (.next ([1515000000000], [120000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([5121000000000], [1344000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([5121000000000, 0], [1530000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([4935000000000, -9000000000000], [1530000000000, 9000000000000]) (some (4, 1, 5)) (some (4,
      1, 5)) (.next ([3825000000000], [1650000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([5001000000000], [2979000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2310000000000],
      [1530000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2496000000000], [4155000000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1530000000000], [2625000000000]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([0, 0], [1530000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1,
      5)) (.next ([-120000000000], [8100000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-120000000000], [1635000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-1344000000000],
      [6465000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1530000000000, -9000000000000],
      [6651000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1530000000000,
      -9000000000000], [6465000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-1650000000000], [5475000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-2979000000000], [7980000000000]) (some (0, 2, 5)) (some (0, 5, 5)) (.next
      ([-1530000000000], [3840000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-4155000000000], [6651000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-2625000000000], [4155000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5,
      4)) (some (0, 5, 4)) (some (0, 5, 4))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded43_5 : ExcludedOn (model43.B 5 ++ [step43.q]) 9000000000000 (model43.caps 5)
    (model43.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2935500000000], [124500000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([4740000000000], [510000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([8100000000000], [1020000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      fan43Owner5Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded43_6 : ExcludedOn (model43.B 6 ++ [step43.q]) 9000000000000 (model43.caps 6)
    (model43.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_7 : ExcludedOn (model43.B 7 ++ [step43.q]) 9000000000000 (model43.caps 7)
    (model43.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_8 : ExcludedOn (model43.B 8 ++ [step43.q]) 9000000000000 (model43.caps 8)
    (model43.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_9 : ExcludedOn (model43.B 9 ++ [step43.q]) 9000000000000 (model43.caps 9)
    (model43.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked43 : StepValid model43 9000000000000 step43 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded43_1
    · exact excluded43_2
    · exact excluded43_3
    · exact excluded43_4
    · exact excluded43_5
    · exact excluded43_6
    · exact excluded43_7
    · exact excluded43_8
    · exact excluded43_9
theorem next43 : model43.insert step43 = model44 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded44_0 : ExcludedOn (model44.B 0 ++ [step44.q]) 9000000000000 (model44.caps 0)
    (model44.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_1 : ExcludedOn (model44.B 1 ++ [step44.q]) 9000000000000 (model44.caps 1)
    (model44.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_2 : ExcludedOn (model44.B 2 ++ [step44.q]) 9000000000000 (model44.caps 2)
    (model44.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_3 : ExcludedOn (model44.B 3 ++ [step44.q]) 9000000000000 (model44.caps 3)
    (model44.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_4 : ExcludedOn (model44.B 4 ++ [step44.q]) 9000000000000 (model44.caps 4)
    (model44.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_5 : ExcludedOn (model44.B 5 ++ [step44.q]) 9000000000000 (model44.caps 5)
    (model44.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2935500000000], [124500000000]) (some (4, 0, 5))
      (some (4, 1, 5)) (.next ([4740000000000], [510000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([3660000000000], [750000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      fan44Owner5Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded44_7 : ExcludedOn (model44.B 7 ++ [step44.q]) 9000000000000 (model44.caps 7)
    (model44.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_8 : ExcludedOn (model44.B 8 ++ [step44.q]) 9000000000000 (model44.caps 8)
    (model44.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_9 : ExcludedOn (model44.B 9 ++ [step44.q]) 9000000000000 (model44.caps 9)
    (model44.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4410000000000], [210000000000]) (some (4, 0, 1))
      (some (4, 1, 2)) (.next ([2250000000000], [630000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([3600000000000, -9000000000000], [1530000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([720000000000, -9000000000000], [630000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([2250000000000], [2250000000000]) (some (4, 1, 2)) (some (4, 1, 3))
      (.next ([4410000000000], [5340000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([2880000000000, -9000000000000], [5340000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([2160000000000], [4710000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0],
      [5130000000000]) (some (4, 1, 3)) (some (4, 1, 4)) (.next ([-210000000000], [4620000000000])
      (some (4, 1, 4)) (some (4, 1, 4)) (.next ([-630000000000], [2880000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-1530000000000, -9000000000000], [5130000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-630000000000], [1350000000000, -9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-2250000000000], [4500000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-5340000000000], [9750000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-5340000000000], [8220000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-4710000000000], [6870000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.terminal (some (0, 1,
      4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem checked44 : StepValid model44 9000000000000 step44 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded44_0
    · exact excluded44_1
    · exact excluded44_2
    · exact excluded44_3
    · exact excluded44_4
    · exact excluded44_5
    · exact (hj rfl).elim
    · exact excluded44_7
    · exact excluded44_8
    · exact excluded44_9
theorem next44 : model44.insert step44 = model45 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded45_0 : ExcludedOn (model45.B 0 ++ [step45.q]) 9000000000000 (model45.caps 0)
    (model45.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_1 : ExcludedOn (model45.B 1 ++ [step45.q]) 9000000000000 (model45.caps 1)
    (model45.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2010000000000, 0], [1020000000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next ([4830000000000], [2910000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([5340000000000], [4410000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([1530000000000, 9000000000000], [1530000000000, 9000000000000]) (some
      (0, 4, 3)) (some (0, 4, 3)) (.next ([3810000000000, -9000000000000], [5940000000000,
      9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([510000000000], [1500000000000])
      (some (0, 4, 3)) (some (4, 4, 3)) (.next ([30000000000, 9000000000000], [480000000000,
      -9000000000000]) (some (4, 4, 3)) (some (4, 4, 3)) (.next ([0, 0], [1530000000000,
      9000000000000]) (some (4, 4, 3)) (some (4, 4, 3)) (.next ([-1020000000000, -9000000000000],
      [3030000000000, 9000000000000]) (some (4, 4, 0)) (some (4, 4, 0)) (.next ([-2910000000000],
      [7740000000000]) (some (4, 4, 0)) (some (4, 2, 0)) (.next ([-4410000000000], [9750000000000])
      (some (4, 2, 0)) (some (4, 2, 0)) (.next ([-1530000000000, -9000000000000], [3060000000000,
      18000000000000]) (some (4, 2, 0)) (some (4, 2, 0)) (.next ([-5940000000000, -9000000000000],
      [9750000000000, 0]) (some (4, 2, 0)) (some (4, 2, 0)) (.next ([-1500000000000],
      [2010000000000]) (some (4, 2, 0)) (some (4, 2, 0)) (.next ([-480000000000, 9000000000000],
      [510000000000]) (some (4, 2, 0)) (some (4, 2, 0)) (.terminal (some (4, 2, 0)) (some (4, 2, 0))
      (some (4, 2, 0))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_2 : ExcludedOn (model45.B 2 ++ [step45.q]) 9000000000000 (model45.caps 2)
    (model45.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_3 : ExcludedOn (model45.B 3 ++ [step45.q]) 9000000000000 (model45.caps 3)
    (model45.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_4 : ExcludedOn (model45.B 4 ++ [step45.q]) 9000000000000 (model45.caps 4)
    (model45.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_5 : ExcludedOn (model45.B 5 ++ [step45.q]) 9000000000000 (model45.caps 5)
    (model45.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2935500000000], [124500000000]) (some (4, 0, 5))
      (some (4, 1, 5)) (.next ([4740000000000], [510000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([5460000000000, 0], [1530000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      fan45Owner5Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded45_7 : ExcludedOn (model45.B 7 ++ [step45.q]) 9000000000000 (model45.caps 7)
    (model45.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_8 : ExcludedOn (model45.B 8 ++ [step45.q]) 9000000000000 (model45.caps 8)
    (model45.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_9 : ExcludedOn (model45.B 9 ++ [step45.q]) 9000000000000 (model45.caps 9)
    (model45.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked45 : StepValid model45 9000000000000 step45 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded45_0
    · exact excluded45_1
    · exact excluded45_2
    · exact excluded45_3
    · exact excluded45_4
    · exact excluded45_5
    · exact (hj rfl).elim
    · exact excluded45_7
    · exact excluded45_8
    · exact excluded45_9
theorem next45 : model45.insert step45 = model46 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded46_0 : ExcludedOn (model46.B 0 ++ [step46.q]) 9000000000000 (model46.caps 0)
    (model46.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_2 : ExcludedOn (model46.B 2 ++ [step46.q]) 9000000000000 (model46.caps 2)
    (model46.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_3 : ExcludedOn (model46.B 3 ++ [step46.q]) 9000000000000 (model46.caps 3)
    (model46.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_4 : ExcludedOn (model46.B 4 ++ [step46.q]) 9000000000000 (model46.caps 4)
    (model46.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_5 : ExcludedOn (model46.B 5 ++ [step46.q]) 9000000000000 (model46.caps 5)
    (model46.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_6 : ExcludedOn (model46.B 6 ++ [step46.q]) 9000000000000 (model46.caps 6)
    (model46.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5340000000000], [780000000000, 9000000000000])
      (some (4, 0, 2)) (some (4, 0, 5)) (.next ([4590000000000], [750000000000]) (some (4, 0, 5))
      (some (4, 0, 5)) (.next ([5340000000000], [3825000000000]) (some (4, 0, 5)) (some (4, 0, 5))
      (.next ([3060000000000, -9000000000000], [2280000000000, 9000000000000]) (some (4, 0, 5))
      (some (4, 0, 5)) (.next ([1530000000000, 9000000000000], [1530000000000, 9000000000000]) (some
      (4, 0, 5)) (some (4, 0, 5)) (.next ([1530000000000, 9000000000000], [4575000000000]) (some (4,
      0, 5)) (some (4, 0, 5)) (.next ([750000000000, 0], [3060000000000, -9000000000000]) (some (4,
      0, 5)) (some (4, 0, 5)) (.next ([780000000000, 9000000000000], [3810000000000,
      -9000000000000]) (some (4, 0, 5)) (some (4, 1, 5)) (.next ([750000000000], [4590000000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([15000000000], [5325000000000]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([0], [3840000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([-780000000000, -9000000000000], [6120000000000, 9000000000000]) (some (0, 1, 5)) (some (0,
      2, 5)) (.next ([-750000000000], [5340000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-3825000000000], [9165000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2280000000000,
      -9000000000000], [5340000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1530000000000,
      -9000000000000], [3060000000000, 18000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-4575000000000, 0], [6105000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-3060000000000, 9000000000000], [3810000000000, -9000000000000]) (some (0, 2, 5)) (some (0,
      2, 5)) (.next ([-3810000000000, 9000000000000], [4590000000000]) (some (0, 2, 5)) (some (0, 2,
      5)) (.next ([-4590000000000], [5340000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-5325000000000], [5340000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded46_7 : ExcludedOn (model46.B 7 ++ [step46.q]) 9000000000000 (model46.caps 7)
    (model46.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_8 : ExcludedOn (model46.B 8 ++ [step46.q]) 9000000000000 (model46.caps 8)
    (model46.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_9 : ExcludedOn (model46.B 9 ++ [step46.q]) 9000000000000 (model46.caps 9)
    (model46.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked46 : StepValid model46 9000000000000 step46 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded46_0
    · exact (hj rfl).elim
    · exact excluded46_2
    · exact excluded46_3
    · exact excluded46_4
    · exact excluded46_5
    · exact excluded46_6
    · exact excluded46_7
    · exact excluded46_8
    · exact excluded46_9
theorem next46 : model46.insert step46 = model47 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded47_1 : ExcludedOn (model47.B 1 ++ [step47.q]) 9000000000000 (model47.caps 1)
    (model47.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4425000000000, 0], [1530000000000,
      9000000000000]) (some (3, 1, 1)) (some (3, 1, 2)) (.next ([4590000000000], [1875000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([3060000000000, -9000000000000], [1875000000000, 0])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2550000000000], [6465000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([0, 0], [1530000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([-1530000000000, -9000000000000], [5955000000000, 9000000000000]) (some (3, 1, 0))
      (some (3, 1, 0)) (.next ([-1875000000000], [6465000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-1875000000000, 0], [4935000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1,
      0)) (.next ([-6465000000000], [9015000000000]) (some (3, 1, 0)) none (.terminal none (some (1,
      1, 3)) none))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded47_2 : ExcludedOn (model47.B 2 ++ [step47.q]) 9000000000000 (model47.caps 2)
    (model47.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7470000000000, -9000000000000], [1530000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([3060000000000, -9000000000000],
      [1875000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1875000000000],
      [2535000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([345000000000, -9000000000000],
      [4065000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0],
      [1530000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-1530000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next
      ([-1875000000000, 0], [4935000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-2535000000000], [4410000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-4065000000000, -9000000000000], [4410000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.terminal (some (0, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded47_3 : ExcludedOn (model47.B 3 ++ [step47.q]) 9000000000000 (model47.caps 3)
    (model47.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_4 : ExcludedOn (model47.B 4 ++ [step47.q]) 9000000000000 (model47.caps 4)
    (model47.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_5 : ExcludedOn (model47.B 5 ++ [step47.q]) 9000000000000 (model47.caps 5)
    (model47.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_6 : ExcludedOn (model47.B 6 ++ [step47.q]) 9000000000000 (model47.caps 6)
    (model47.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_7 : ExcludedOn (model47.B 7 ++ [step47.q]) 9000000000000 (model47.caps 7)
    (model47.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_8 : ExcludedOn (model47.B 8 ++ [step47.q]) 9000000000000 (model47.caps 8)
    (model47.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_9 : ExcludedOn (model47.B 9 ++ [step47.q]) 9000000000000 (model47.caps 9)
    (model47.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked47 : StepValid model47 9000000000000 step47 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded47_1
    · exact excluded47_2
    · exact excluded47_3
    · exact excluded47_4
    · exact excluded47_5
    · exact excluded47_6
    · exact excluded47_7
    · exact excluded47_8
    · exact excluded47_9
theorem next47 : model47.insert step47 = model48 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint170000180000
end ConwaySoifer.Simplified.Certificates
