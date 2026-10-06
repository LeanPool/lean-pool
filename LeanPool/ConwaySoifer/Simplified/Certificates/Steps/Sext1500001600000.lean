/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext150000160000
import Mathlib.Tactic.FinCases

/-!
# Sext 150000 160000 0

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
namespace Sext150000160000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan4Owner0Part0 : FanWitness := (.next ([3225000000000], [6150000000000]) (some (0, 6, 6)) (some
    (0, 6, 6)) (.next ([2400000000000], [5250000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next
    ([2778000000000, 2520000000000], [6978000000000, 2520000000000]) (some (0, 6, 3)) (some (0, 6,
    3)) (.next ([2700000000000], [7050000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next
    ([2022000000000, -2520000000000], [7356000000000, 5040000000000]) (some (0, 6, 3)) (some (0, 6,
    3)) (.next ([1644000000000, -5040000000000], [6978000000000, 2520000000000]) (some (0, 6, 3))
    (some (0, 6, 3)) (.next ([300000000000], [1800000000000]) (some (0, 6, 3)) (some (0, 6, 3))
    (.next ([3000000000, 2520000000000], [1203000000000, 2520000000000]) (some (0, 6, 3)) (some (0,
    6, 3)) (.next ([0, 0], [1134000000000, 7560000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next
    ([-72000000000, 2520000000000], [1128000000000, 2520000000000]) (some (0, 6, 3)) (some (0, 6,
    3)) (.next ([-378000000000, -2520000000000], [2106000000000, 5040000000000]) (some (0, 6, 3))
    (some (0, 6, 3)) (.next ([-756000000000, -5040000000000], [1728000000000, 2520000000000]) (some
    (0, 6, 3)) (some (0, 6, 3)) (.next ([-753000000000, -2520000000000], [1581000000000,
    5040000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([-378000000000, -2520000000000],
    [756000000000, 5040000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([-900000000000],
    [1725000000000]) (some (0, 6, 3)) (some (1, 6, 3)) (.next ([-525000000000], [900000000000])
    (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-6150000000000], [9375000000000]) (some (1, 6, 4))
    (some (1, 6, 4)) (.next ([-5250000000000], [7650000000000]) (some (1, 6, 4)) (some (1, 6, 4))
    (.next ([-6978000000000, -2520000000000], [9756000000000, 5040000000000]) (some (1, 6, 4)) (some
    (1, 6, 4)) (.next ([-7050000000000], [9750000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next
    ([-7356000000000, -5040000000000], [9378000000000, 2520000000000]) (some (1, 6, 4)) (some (1, 6,
    4)) (.next ([-6978000000000, -2520000000000], [8622000000000, -2520000000000]) (some (1, 6, 4))
    (some (1, 6, 4)) (.next ([-1800000000000], [2100000000000]) (some (1, 6, 4)) (some (6, 6, 4))
    (.next ([-1203000000000, -2520000000000], [1206000000000, 5040000000000]) (some (6, 6, 4)) (some
    (6, 6, 4)) (.terminal (some (6, 6, 4)) (some (6, 6, 4)) (some (6, 6,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan5Owner0Part0 : FanWitness := (.next ([825000000000], [900000000000]) (some (6, 6, 2)) (some
    (6, 6, 2)) (.next ([306000000000, 5040000000000], [372000000000, -2520000000000]) (some (6, 6,
    2)) (some (6, 6, 3)) (.next ([375000000000], [525000000000]) (some (6, 6, 3)) (some (6, 6, 3))
    (.next ([378000000000, 2520000000000], [1728000000000, 2520000000000]) (some (6, 6, 3)) (some
    (6, 6, 3)) (.next ([300000000000], [1800000000000]) (some (6, 6, 3)) (some (6, 6, 3)) (.next
    ([3000000000, 2520000000000], [1203000000000, 2520000000000]) (some (6, 6, 3)) (some (6, 6, 3))
    (.next ([0, 0], [1134000000000, 7560000000000]) (some (6, 6, 3)) (some (6, 6, 3)) (.next
    ([-72000000000, 2520000000000], [1128000000000, 2520000000000]) (some (6, 6, 3)) (some (6, 6,
    3)) (.next ([-378000000000, -2520000000000], [2106000000000, 5040000000000]) (some (6, 6, 3))
    (some (6, 6, 3)) (.next ([-2250000000000], [9000000000000]) (some (6, 6, 3)) (some (6, 6, 3))
    (.next ([-3222000000000, 2520000000000], [8244000000000, -5040000000000]) (some (6, 2, 3)) (some
    (6, 2, 3)) (.next ([-3975000000000], [9825000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next
    ([-756000000000, -5040000000000], [1728000000000, 2520000000000]) (some (6, 2, 3)) (some (6, 2,
    3)) (.next ([-3978000000000, -2520000000000], [8622000000000, -2520000000000]) (some (6, 2, 3))
    (some (6, 2, 3)) (.next ([-4356000000000, -5040000000000], [9378000000000, 2520000000000]) (some
    (6, 2, 3)) (some (6, 2, 3)) (.next ([-4350000000000], [9300000000000]) (some (6, 2, 3)) (some
    (6, 2, 3)) (.next ([-753000000000, -2520000000000], [1581000000000, 5040000000000]) (some (6, 2,
    3)) (some (6, 2, 3)) (.next ([-378000000000, -2520000000000], [756000000000, 5040000000000])
    (some (6, 2, 3)) (some (6, 2, 3)) (.next ([-900000000000], [1725000000000]) (some (6, 2, 3))
    (some (6, 2, 3)) (.next ([-372000000000, 2520000000000], [678000000000, 2520000000000]) (some
    (6, 2, 3)) (some (6, 2, 3)) (.next ([-525000000000], [900000000000]) (some (6, 2, 4)) (some (6,
    2, 4)) (.next ([-1728000000000, -2520000000000], [2106000000000, 5040000000000]) (some (6, 2,
    4)) (some (6, 2, 4)) (.next ([-1800000000000], [2100000000000]) (some (6, 2, 4)) (some (6, 2,
    4)) (.next ([-1203000000000, -2520000000000], [1206000000000, 5040000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.terminal (some (6, 2, 4)) (some (6, 2, 4)) (some (6, 2,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan5Owner0Part1 : FanWitness := (.next ([825000000000], [900000000000]) (some (6, 6, 2)) (some
    (6, 6, 2)) (.next ([375000000000], [525000000000]) (some (6, 6, 2)) (some (6, 6, 3)) (.next
    ([378000000000, 2520000000000], [1728000000000, 2520000000000]) (some (6, 6, 3)) (some (6, 6,
    3)) (.next ([300000000000], [1800000000000]) (some (6, 6, 3)) (some (6, 6, 3)) (.next
    ([3000000000, 2520000000000], [1203000000000, 2520000000000]) (some (6, 6, 3)) (some (6, 6, 3))
    (.next ([0, 0], [1134000000000, 7560000000000]) (some (6, 6, 3)) (some (6, 6, 3)) (.next
    ([-72000000000, 2520000000000], [1128000000000, 2520000000000]) (some (6, 6, 3)) (some (6, 6,
    3)) (.next ([-378000000000, -2520000000000], [2106000000000, 5040000000000]) (some (6, 6, 3))
    (some (6, 6, 3)) (.next ([-2250000000000], [9000000000000]) (some (6, 6, 3)) (some (6, 6, 3))
    (.next ([-3222000000000, 2520000000000], [8244000000000, -5040000000000]) (some (6, 2, 3)) (some
    (6, 2, 3)) (.next ([-3975000000000], [9825000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next
    ([-756000000000, -5040000000000], [1728000000000, 2520000000000]) (some (6, 2, 3)) (some (6, 2,
    3)) (.next ([-3978000000000, -2520000000000], [8622000000000, -2520000000000]) (some (6, 2, 3))
    (some (6, 2, 3)) (.next ([-4356000000000, -5040000000000], [9378000000000, 2520000000000]) (some
    (6, 2, 3)) (some (6, 2, 3)) (.next ([-4350000000000], [9300000000000]) (some (6, 2, 3)) (some
    (6, 2, 3)) (.next ([-753000000000, -2520000000000], [1581000000000, 5040000000000]) (some (6, 2,
    3)) (some (6, 2, 3)) (.next ([-378000000000, -2520000000000], [756000000000, 5040000000000])
    (some (6, 2, 3)) (some (6, 2, 3)) (.next ([-447000000000, 2520000000000], [828000000000,
    2520000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next ([-372000000000, 2520000000000],
    [678000000000, 2520000000000]) (some (6, 2, 3)) (some (6, 2, 4)) (.next ([-900000000000],
    [1725000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-525000000000], [900000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-1728000000000, -2520000000000], [2106000000000,
    5040000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-1800000000000], [2100000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-1203000000000, -2520000000000], [1206000000000,
    5040000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.terminal (some (6, 2, 4)) (some (6, 2, 4))
    (some (6, 2, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan5Owner0Part2 : FanWitness := (.next ([4950000000000], [4350000000000]) (some (4, 6, 2)) (some
    (4, 6, 2)) (.next ([828000000000, 2520000000000], [753000000000, 2520000000000]) (some (4, 6,
    2)) (some (6, 6, 2)) (.next ([306000000000, 5040000000000], [372000000000, -2520000000000])
    (some (6, 6, 2)) (some (6, 6, 2)) (.next ([825000000000], [900000000000]) (some (6, 6, 2)) (some
    (6, 6, 2)) (.next ([375000000000], [525000000000]) (some (6, 6, 2)) (some (6, 6, 3)) (.next
    ([378000000000, 2520000000000], [1728000000000, 2520000000000]) (some (6, 6, 3)) (some (6, 6,
    3)) (.next ([300000000000], [1800000000000]) (some (6, 6, 3)) (some (6, 6, 3)) (.next
    ([3000000000, 2520000000000], [1203000000000, 2520000000000]) (some (6, 6, 3)) (some (6, 6, 3))
    (.next ([0, 0], [1134000000000, 7560000000000]) (some (6, 6, 3)) (some (6, 6, 3)) (.next
    ([-72000000000, 2520000000000], [1128000000000, 2520000000000]) (some (6, 6, 3)) (some (6, 6,
    3)) (.next ([-378000000000, -2520000000000], [2106000000000, 5040000000000]) (some (6, 6, 3))
    (some (6, 6, 3)) (.next ([-2250000000000], [9000000000000]) (some (6, 6, 3)) (some (6, 6, 3))
    (.next ([-3222000000000, 2520000000000], [8244000000000, -5040000000000]) (some (6, 2, 3)) (some
    (6, 2, 3)) (.next ([-3975000000000], [9825000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next
    ([-756000000000, -5040000000000], [1728000000000, 2520000000000]) (some (6, 2, 3)) (some (6, 2,
    3)) (.next ([-3978000000000, -2520000000000], [8622000000000, -2520000000000]) (some (6, 2, 3))
    (some (6, 2, 3)) (.next ([-4350000000000], [9300000000000]) (some (6, 2, 3)) (some (6, 2, 3))
    (.next ([-753000000000, -2520000000000], [1581000000000, 5040000000000]) (some (6, 2, 3)) (some
    (6, 2, 3)) (.next ([-372000000000, 2520000000000], [678000000000, 2520000000000]) (some (6, 2,
    3)) (some (6, 2, 3)) (.next ([-900000000000], [1725000000000]) (some (6, 2, 3)) (some (6, 2, 4))
    (.next ([-525000000000], [900000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-1728000000000, -2520000000000], [2106000000000, 5040000000000]) (some (6, 2, 4)) (some (6, 2,
    4)) (.next ([-1800000000000], [2100000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-1203000000000, -2520000000000], [1206000000000, 5040000000000]) (some (6, 2, 4)) (some (6, 2,
    4)) (.terminal (some (6, 2, 4)) (some (6, 2, 4)) (some (6, 2, 4)))))))))))))))))))))))))))

theorem excluded0_1 : ExcludedOn (model0.B 1 ++ [step0.q]) 9000000000000 (model0.caps 1) (model0.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded0_2 : ExcludedOn (model0.B 2 ++ [step0.q]) 9000000000000 (model0.caps 2) (model0.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7350000000000, -9000000000000], [900000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1350000000000, 9000000000000],
      [1350000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1800000000000,
      9000000000000], [6900000000000, -9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([450000000000], [8250000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0, 0],
      [1350000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-900000000000,
      -9000000000000], [8250000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([-1350000000000,
      -9000000000000], [2700000000000, 18000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next
      ([-6900000000000, 9000000000000], [8700000000000, 0]) (some (3, 3, 2)) (some (3, 3, 2)) (.next
      ([-8250000000000], [8700000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded0_3 : ExcludedOn (model0.B 3 ++ [step0.q]) 9000000000000 (model0.caps 3) (model0.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8250000000000], [300000000000]) (some (1, 0, 3))
      (some (2, 0, 3)) (.next ([6900000000000, -9000000000000], [1650000000000, 9000000000000])
      (some (2, 0, 3)) (some (2, 0, 3)) (.next ([1350000000000, 9000000000000], [1350000000000,
      9000000000000]) (some (2, 0, 3)) (some (2, 3, 3)) (.next ([1050000000000, 9000000000000],
      [7200000000000, -9000000000000]) (some (2, 3, 3)) (some (2, 3, 3)) (.next ([0],
      [1350000000000, 9000000000000]) (some (2, 3, 1)) (some (2, 3, 1)) (.next ([-300000000000],
      [8550000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-1650000000000, -9000000000000],
      [8550000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-1350000000000, -9000000000000],
      [2700000000000, 18000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-7200000000000,
      9000000000000], [8250000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.terminal (some (0, 3, 1))
      (some (0, 3, 1)) (some (0, 3, 1))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded0_4 : ExcludedOn (model0.B 4 ++ [step0.q]) 9000000000000 (model0.caps 4) (model0.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8550000000000], [750000000000]) (some (2, 0, 3))
      (some (2, 1, 3)) (.next ([7200000000000, -9000000000000], [2100000000000, 9000000000000])
      (some (2, 1, 3)) (some (2, 1, 3)) (.next ([1350000000000, 9000000000000], [1350000000000,
      9000000000000]) (some (2, 1, 3)) (some (2, 1, 3)) (.next ([600000000000, 9000000000000],
      [7950000000000, -9000000000000]) (some (2, 1, 3)) (some (2, 1, 3)) (.next ([0, 0],
      [1350000000000, 9000000000000]) (some (2, 1, 3)) (some (2, 1, 3)) (.next ([-750000000000],
      [9300000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2100000000000, -9000000000000],
      [9300000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1350000000000,
      -9000000000000], [2700000000000, 18000000000000]) (some (0, 1, 3)) (some (0, 3, 3)) (.next
      ([-7950000000000, 9000000000000], [8550000000000]) (some (0, 3, 3)) (some (0, 3, 3))
      (.terminal (some (0, 3, 2)) (some (0, 3, 2)) (some (0, 3, 2))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded0_5 : ExcludedOn (model0.B 5 ++ [step0.q]) 9000000000000 (model0.caps 5) (model0.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded0_6 : ExcludedOn (model0.B 6 ++ [step0.q]) 9000000000000 (model0.caps 6) (model0.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded0_7 : ExcludedOn (model0.B 7 ++ [step0.q]) 9000000000000 (model0.caps 7) (model0.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded0_8 : ExcludedOn (model0.B 8 ++ [step0.q]) 9000000000000 (model0.caps 8) (model0.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded0_9 : ExcludedOn (model0.B 9 ++ [step0.q]) 9000000000000 (model0.caps 9) (model0.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked0 : StepValid model0 9000000000000 step0 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded0_1
    · exact excluded0_2
    · exact excluded0_3
    · exact excluded0_4
    · exact excluded0_5
    · exact excluded0_6
    · exact excluded0_7
    · exact excluded0_8
    · exact excluded0_9
theorem next0 : model0.insert step0 = model1 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded1_1 : ExcludedOn (model1.B 1 ++ [step1.q]) 9000000000000 (model1.caps 1) (model1.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7200000000000, -9000000000000], [975000000000,
      9000000000000]) (some (0, 3, 1)) none (.next ([1350000000000, 9000000000000], [1350000000000,
      9000000000000]) none none (.next ([1725000000000, 9000000000000], [6825000000000,
      -9000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next ([375000000000], [8175000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [1350000000000, 9000000000000]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([-975000000000, -9000000000000], [8175000000000, 0]) (some (3, 1,
      0)) (some (3, 1, 0)) (.next ([-1350000000000, -9000000000000], [2700000000000,
      18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-6825000000000, 9000000000000],
      [8550000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-8175000000000], [8550000000000])
      (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1,
      0))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded1_2 : ExcludedOn (model1.B 2 ++ [step1.q]) 9000000000000 (model1.caps 2) (model1.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8175000000000], [450000000000]) (some (0, 3, 1))
      (some (0, 3, 1)) (.next ([6825000000000, -9000000000000], [1800000000000, 9000000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1350000000000, 9000000000000], [1350000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([900000000000, 9000000000000],
      [7275000000000, -9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0, 0],
      [1350000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-450000000000],
      [8625000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([-1800000000000, -9000000000000],
      [8625000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-1350000000000, -9000000000000],
      [2700000000000, 18000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-7275000000000,
      9000000000000], [8175000000000, 0]) (some (3, 3, 2)) (some (3, 3, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded1_3 : ExcludedOn (model1.B 3 ++ [step1.q]) 9000000000000 (model1.caps 3) (model1.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded1_4 : ExcludedOn (model1.B 4 ++ [step1.q]) 9000000000000 (model1.caps 4) (model1.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded1_5 : ExcludedOn (model1.B 5 ++ [step1.q]) 9000000000000 (model1.caps 5) (model1.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded1_6 : ExcludedOn (model1.B 6 ++ [step1.q]) 9000000000000 (model1.caps 6) (model1.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2175000000000, 9000000000000], [7200000000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([1725000000000, 9000000000000],
      [6825000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1350000000000,
      9000000000000], [7650000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([825000000000], [8550000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [1350000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-7200000000000,
      9000000000000], [9375000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-6825000000000,
      9000000000000], [8550000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-7650000000000,
      9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 3)) (.next
      ([-8550000000000], [9375000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1,
      3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded1_7 : ExcludedOn (model1.B 7 ++ [step1.q]) 9000000000000 (model1.caps 7) (model1.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded1_8 : ExcludedOn (model1.B 8 ++ [step1.q]) 9000000000000 (model1.caps 8) (model1.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded1_9 : ExcludedOn (model1.B 9 ++ [step1.q]) 9000000000000 (model1.caps 9) (model1.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked1 : StepValid model1 9000000000000 step1 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded1_1
    · exact excluded1_2
    · exact excluded1_3
    · exact excluded1_4
    · exact excluded1_5
    · exact excluded1_6
    · exact excluded1_7
    · exact excluded1_8
    · exact excluded1_9
theorem next1 : model1.insert step1 = model2 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded2_1 : ExcludedOn (model2.B 1 ++ [step2.q]) 9000000000000 (model2.caps 1) (model2.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7650000000000], [1350000000000]) (some (0, 3,
      1)) (some (0, 3, 2)) (.next ([6300000000000, -9000000000000], [2700000000000, 9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([1350000000000, 9000000000000], [1350000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([0, 9000000000000], [7650000000000,
      -9000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next ([0, 0], [1350000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1350000000000], [9000000000000])
      (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2700000000000, -9000000000000], [9000000000000,
      0]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1350000000000, -9000000000000],
      [2700000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-7650000000000,
      9000000000000], [7650000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1, 0))
      (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded2_2 : ExcludedOn (model2.B 2 ++ [step2.q]) 9000000000000 (model2.caps 2) (model2.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded2_3 : ExcludedOn (model2.B 3 ++ [step2.q]) 9000000000000 (model2.caps 3) (model2.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded2_4 : ExcludedOn (model2.B 4 ++ [step2.q]) 9000000000000 (model2.caps 4) (model2.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded2_5 : ExcludedOn (model2.B 5 ++ [step2.q]) 9000000000000 (model2.caps 5) (model2.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7650000000000, -9000000000000], [0,
      9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([1350000000000, 9000000000000],
      [1350000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([2700000000000,
      9000000000000], [6300000000000, -9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next
      ([1350000000000], [7650000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0],
      [1350000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, -9000000000000],
      [7650000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-1350000000000, -9000000000000],
      [2700000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-6300000000000,
      9000000000000], [9000000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-7650000000000], [9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded2_6 : ExcludedOn (model2.B 6 ++ [step2.q]) 9000000000000 (model2.caps 6) (model2.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1350000000000, 9000000000000], [6300000000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([1350000000000, 9000000000000],
      [7650000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 9000000000000],
      [7650000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [1350000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-6300000000000,
      9000000000000], [7650000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-7650000000000,
      9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-7650000000000,
      9000000000000], [7650000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2))
      (some (0, 1, 3)) (some (0, 1, 3))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded2_7 : ExcludedOn (model2.B 7 ++ [step2.q]) 9000000000000 (model2.caps 7) (model2.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded2_8 : ExcludedOn (model2.B 8 ++ [step2.q]) 9000000000000 (model2.caps 8) (model2.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded2_9 : ExcludedOn (model2.B 9 ++ [step2.q]) 9000000000000 (model2.caps 9) (model2.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked2 : StepValid model2 9000000000000 step2 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded2_1
    · exact excluded2_2
    · exact excluded2_3
    · exact excluded2_4
    · exact excluded2_5
    · exact excluded2_6
    · exact excluded2_7
    · exact excluded2_8
    · exact excluded2_9
theorem next2 : model2.insert step2 = model3 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded3_0 : ExcludedOn (model3.B 0 ++ [step3.q]) 9000000000000 (model3.caps 0) (model3.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded3_1 : ExcludedOn (model3.B 1 ++ [step3.q]) 9000000000000 (model3.caps 1) (model3.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded3_2 : ExcludedOn (model3.B 2 ++ [step3.q]) 9000000000000 (model3.caps 2) (model3.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded3_3 : ExcludedOn (model3.B 3 ++ [step3.q]) 9000000000000 (model3.caps 3) (model3.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded3_4 : ExcludedOn (model3.B 4 ++ [step3.q]) 9000000000000 (model3.caps 4) (model3.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded3_5 : ExcludedOn (model3.B 5 ++ [step3.q]) 9000000000000 (model3.caps 5) (model3.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded3_6 : ExcludedOn (model3.B 6 ++ [step3.q]) 9000000000000 (model3.caps 6) (model3.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([825000000000, 0], [525000000000, 9000000000000])
      (some (2, 0, 1)) (some (2, 0, 2)) (.next ([1350000000000, 9000000000000], [7650000000000,
      -9000000000000]) (some (2, 0, 2)) (some (2, 3, 2)) (.next ([0, 0], [1350000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-525000000000, -9000000000000],
      [1350000000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-7650000000000,
      9000000000000], [9000000000000, 0]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some (0, 3,
      2)) (some (0, 1, 2)) (some (0, 3, 2))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded3_7 : ExcludedOn (model3.B 7 ++ [step3.q]) 9000000000000 (model3.caps 7) (model3.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded3_8 : ExcludedOn (model3.B 8 ++ [step3.q]) 9000000000000 (model3.caps 8) (model3.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked3 : StepValid model3 9000000000000 step3 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded3_0
    · exact excluded3_1
    · exact excluded3_2
    · exact excluded3_3
    · exact excluded3_4
    · exact excluded3_5
    · exact excluded3_6
    · exact excluded3_7
    · exact excluded3_8
    · exact (hj rfl).elim
theorem next3 : model3.insert step3 = model4 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded4_0 : ExcludedOn (model4.B 0 ++ [step4.q]) 9000000000000 (model4.caps 0) (model4.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1056000000000, 5040000000000], [72000000000,
      -2520000000000]) (some (4, 6, 6)) (some (4, 6, 6)) (.next ([1728000000000, 2520000000000],
      [378000000000, 2520000000000]) (some (4, 6, 6)) (some (4, 6, 6)) (.next ([972000000000,
      -2520000000000], [756000000000, 5040000000000]) (some (4, 6, 6)) (some (4, 6, 6)) (.next
      ([828000000000, 2520000000000], [753000000000, 2520000000000]) (some (5, 6, 6)) (some (5, 6,
      6)) (.next ([378000000000, 2520000000000], [378000000000, 2520000000000]) (some (5, 6, 6))
      (some (5, 6, 6)) (.next ([825000000000], [900000000000]) (some (5, 6, 6)) (some (5, 6, 6))
      (.next ([375000000000], [525000000000]) (some (0, 6, 6)) (some (0, 6, 6))
      fan4Owner0Part0)))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100 (by decide +kernel)
  decide +kernel

theorem excluded4_1 : ExcludedOn (model4.B 1 ++ [step4.q]) 9000000000000 (model4.caps 1) (model4.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded4_2 : ExcludedOn (model4.B 2 ++ [step4.q]) 9000000000000 (model4.caps 2) (model4.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded4_3 : ExcludedOn (model4.B 3 ++ [step4.q]) 9000000000000 (model4.caps 3) (model4.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded4_4 : ExcludedOn (model4.B 4 ++ [step4.q]) 9000000000000 (model4.caps 4) (model4.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded4_6 : ExcludedOn (model4.B 6 ++ [step4.q]) 9000000000000 (model4.caps 6) (model4.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded4_7 : ExcludedOn (model4.B 7 ++ [step4.q]) 9000000000000 (model4.caps 7) (model4.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded4_8 : ExcludedOn (model4.B 8 ++ [step4.q]) 9000000000000 (model4.caps 8) (model4.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded4_9 : ExcludedOn (model4.B 9 ++ [step4.q]) 9000000000000 (model4.caps 9) (model4.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6600000000000, 0], [1050000000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 1, 2)) (.next ([6600000000000], [2400000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([825000000000], [1575000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([1350000000000, 9000000000000], [6825000000000, -9000000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [1350000000000, 9000000000000]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([-1050000000000, 9000000000000], [7650000000000, -9000000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2400000000000], [9000000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-1575000000000], [2400000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-6825000000000, 9000000000000], [8175000000000, 0]) (some (0, 1, 2)) (some (0, 1, 3))
      (.terminal (some (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem checked4 : StepValid model4 9000000000000 step4 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded4_0
    · exact excluded4_1
    · exact excluded4_2
    · exact excluded4_3
    · exact excluded4_4
    · exact (hj rfl).elim
    · exact excluded4_6
    · exact excluded4_7
    · exact excluded4_8
    · exact excluded4_9
theorem next4 : model4.insert step4 = model5 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded5_0 : ExcludedOn (model5.B 0 ++ [step5.q]) 9000000000000 (model5.caps 0) (model5.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (10) (21) (2100) (.witnessedFan (.next ([1056000000000,
      5040000000000], [72000000000, -2520000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next
      ([1728000000000, 2520000000000], [378000000000, 2520000000000]) (some (4, 6, 2)) (some (4, 6,
      2)) (.next ([6750000000000], [2250000000000]) (some (4, 6, 2)) (some (5, 6, 2)) (.next
      ([5022000000000, -2520000000000], [3222000000000, -2520000000000]) (some (5, 6, 2)) (some (5,
      6, 2)) (.next ([5850000000000], [3975000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
      ([972000000000, -2520000000000], [756000000000, 5040000000000]) (some (5, 6, 2)) (some (5, 6,
      2)) (.next ([4644000000000, -5040000000000], [3978000000000, 2520000000000]) (some (5, 6, 2))
      (some (5, 6, 2)) (.next ([5022000000000, -2520000000000], [4356000000000, 5040000000000])
      (some (5, 6, 2)) (some (5, 6, 2)) (.next ([4950000000000], [4350000000000]) (some (5, 6, 2))
      (some (5, 6, 2)) (.next ([828000000000, 2520000000000], [753000000000, 2520000000000]) (some
      (5, 6, 2)) (some (6, 6, 2)) (.next ([378000000000, 2520000000000], [378000000000,
      2520000000000]) (some (6, 6, 2)) (some (6, 6, 2)) fan5Owner0Part0)))))))))))) (.split (170)
      (270) (357) (35700) (.witnessedFan (.next ([1056000000000, 5040000000000], [72000000000,
      -2520000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next ([1728000000000, 2520000000000],
      [378000000000, 2520000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next ([6750000000000],
      [2250000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next ([5022000000000, -2520000000000],
      [3222000000000, -2520000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next ([5850000000000],
      [3975000000000]) (some (4, 6, 2)) (some (5, 6, 2)) (.next ([972000000000, -2520000000000],
      [756000000000, 5040000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([4644000000000,
      -5040000000000], [3978000000000, 2520000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
      ([5022000000000, -2520000000000], [4356000000000, 5040000000000]) (some (5, 6, 2)) (some (5,
      6, 2)) (.next ([4950000000000], [4350000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
      ([828000000000, 2520000000000], [753000000000, 2520000000000]) (some (5, 6, 2)) (some (6, 6,
      2)) (.next ([378000000000, 2520000000000], [378000000000, 2520000000000]) (some (6, 6, 2))
      (some (6, 6, 2)) (.next ([381000000000, 5040000000000], [447000000000, -2520000000000]) (some
      (6, 6, 2)) (some (6, 6, 2)) (.next ([306000000000, 5040000000000], [372000000000,
      -2520000000000]) (some (6, 6, 2)) (some (6, 6, 2)) fan5Owner0Part1))))))))))))))
      (.witnessedFan (.next ([1056000000000, 5040000000000], [72000000000, -2520000000000]) (some
      (4, 6, 2)) (some (4, 6, 2)) (.next ([1728000000000, 2520000000000], [378000000000,
      2520000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next ([6750000000000], [2250000000000])
      (some (4, 6, 2)) (some (4, 6, 2)) (.next ([5022000000000, -2520000000000], [3222000000000,
      -2520000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next ([5850000000000], [3975000000000])
      (some (4, 6, 2)) (some (4, 6, 2)) (.next ([972000000000, -2520000000000], [756000000000,
      5040000000000]) (some (4, 6, 2)) (some (4, 6, 2)) (.next ([4644000000000, -5040000000000],
      [3978000000000, 2520000000000]) (some (4, 6, 2)) (some (4, 6, 2)) fan5Owner0Part2))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded5_1 : ExcludedOn (model5.B 1 ++ [step5.q]) 9000000000000 (model5.caps 1) (model5.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded5_2 : ExcludedOn (model5.B 2 ++ [step5.q]) 9000000000000 (model5.caps 2) (model5.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded5_3 : ExcludedOn (model5.B 3 ++ [step5.q]) 9000000000000 (model5.caps 3) (model5.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded5_5 : ExcludedOn (model5.B 5 ++ [step5.q]) 9000000000000 (model5.caps 5) (model5.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded5_6 : ExcludedOn (model5.B 6 ++ [step5.q]) 9000000000000 (model5.caps 6) (model5.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded5_7 : ExcludedOn (model5.B 7 ++ [step5.q]) 9000000000000 (model5.caps 7) (model5.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded5_8 : ExcludedOn (model5.B 8 ++ [step5.q]) 9000000000000 (model5.caps 8) (model5.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded5_9 : ExcludedOn (model5.B 9 ++ [step5.q]) 9000000000000 (model5.caps 9) (model5.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked5 : StepValid model5 9000000000000 step5 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded5_0
    · exact excluded5_1
    · exact excluded5_2
    · exact excluded5_3
    · exact (hj rfl).elim
    · exact excluded5_5
    · exact excluded5_6
    · exact excluded5_7
    · exact excluded5_8
    · exact excluded5_9
theorem next5 : model5.insert step5 = model6 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded6_1 : ExcludedOn (model6.B 1 ++ [step6.q]) 9000000000000 (model6.caps 1) (model6.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5400000000000], [3150000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([5400000000000], [4500000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([1350000000000, 9000000000000], [1350000000000, 9000000000000]) (some
      (0, 3, 2)) (some (0, 3, 2)) (.next ([4050000000000, -9000000000000], [5850000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [1350000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-3150000000000, 9000000000000],
      [8550000000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-4500000000000],
      [9900000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1350000000000, -9000000000000],
      [2700000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-5850000000000,
      -9000000000000], [9900000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
      0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded6_2 : ExcludedOn (model6.B 2 ++ [step6.q]) 9000000000000 (model6.caps 2) (model6.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded6_3 : ExcludedOn (model6.B 3 ++ [step6.q]) 9000000000000 (model6.caps 3) (model6.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded6_4 : ExcludedOn (model6.B 4 ++ [step6.q]) 9000000000000 (model6.caps 4) (model6.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded6_5 : ExcludedOn (model6.B 5 ++ [step6.q]) 9000000000000 (model6.caps 5) (model6.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4950000000000, 9000000000000], [3150000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([3600000000000], [4500000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([1500000000000], [3000000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([1350000000000, 9000000000000], [6600000000000, 0]) (some (0, 1, 2))
      (some (0, 1, 3)) (.next ([0, 0], [1350000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([-3150000000000, 9000000000000], [8100000000000, 0]) (some (0, 1, 3)) (some (0, 2,
      3)) (.next ([-4500000000000], [8100000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-3000000000000], [4500000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-6600000000000,
      0], [7950000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded6_6 : ExcludedOn (model6.B 6 ++ [step6.q]) 9000000000000 (model6.caps 6) (model6.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4500000000000], [900000000000]) (some (2, 0, 1))
      (some (2, 0, 2)) (.next ([5400000000000], [3150000000000, -9000000000000]) (some (2, 0, 2))
      (some (2, 0, 2)) (.next ([1350000000000, 9000000000000], [7650000000000, -9000000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([450000000000, 9000000000000], [4050000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1350000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-900000000000], [5400000000000])
      (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-3150000000000, 9000000000000], [8550000000000,
      -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-7650000000000, 9000000000000],
      [9000000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-4050000000000, 9000000000000],
      [4500000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded6_7 : ExcludedOn (model6.B 7 ++ [step6.q]) 9000000000000 (model6.caps 7) (model6.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded6_8 : ExcludedOn (model6.B 8 ++ [step6.q]) 9000000000000 (model6.caps 8) (model6.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded6_9 : ExcludedOn (model6.B 9 ++ [step6.q]) 9000000000000 (model6.caps 9) (model6.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked6 : StepValid model6 9000000000000 step6 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded6_1
    · exact excluded6_2
    · exact excluded6_3
    · exact excluded6_4
    · exact excluded6_5
    · exact excluded6_6
    · exact excluded6_7
    · exact excluded6_8
    · exact excluded6_9
theorem next6 : model6.insert step6 = model7 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded7_1 : ExcludedOn (model7.B 1 ++ [step7.q]) 9000000000000 (model7.caps 1) (model7.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4950000000000], [3600000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([1350000000000, 9000000000000], [1350000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([3600000000000, -9000000000000],
      [6300000000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0],
      [1350000000000, 9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-3600000000000,
      9000000000000], [8550000000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next
      ([-1350000000000, -9000000000000], [2700000000000, 18000000000000]) (some (3, 1, 0)) (some (3,
      1, 0)) (.next ([-6300000000000, -9000000000000], [9900000000000, 0]) (some (3, 1, 0)) (some
      (3, 1, 0)) (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded7_2 : ExcludedOn (model7.B 2 ++ [step7.q]) 9000000000000 (model7.caps 2) (model7.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded7_3 : ExcludedOn (model7.B 3 ++ [step7.q]) 9000000000000 (model7.caps 3) (model7.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded7_4 : ExcludedOn (model7.B 4 ++ [step7.q]) 9000000000000 (model7.caps 4) (model7.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded7_5 : ExcludedOn (model7.B 5 ++ [step7.q]) 9000000000000 (model7.caps 5) (model7.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5400000000000, 9000000000000], [2700000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([4050000000000], [4050000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([1500000000000], [2550000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([1350000000000, 9000000000000], [6600000000000, 0]) (some (0, 1, 2))
      (some (0, 1, 3)) (.next ([0, 0], [1350000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([-2700000000000, 9000000000000], [8100000000000, 0]) (some (0, 1, 3)) (some (0, 2,
      3)) (.next ([-4050000000000], [8100000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-2550000000000], [4050000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-6600000000000,
      0], [7950000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded7_6 : ExcludedOn (model7.B 6 ++ [step7.q]) 9000000000000 (model7.caps 6) (model7.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4050000000000], [900000000000]) (some (2, 0, 1))
      (some (2, 0, 2)) (.next ([4950000000000], [3600000000000, -9000000000000]) (some (2, 0, 2))
      (some (2, 0, 2)) (.next ([1350000000000, 9000000000000], [7650000000000, -9000000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([450000000000, 9000000000000], [3600000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1350000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-900000000000], [4950000000000])
      (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-3600000000000, 9000000000000], [8550000000000,
      -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-7650000000000, 9000000000000],
      [9000000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3600000000000, 9000000000000],
      [4050000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded7_7 : ExcludedOn (model7.B 7 ++ [step7.q]) 9000000000000 (model7.caps 7) (model7.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded7_8 : ExcludedOn (model7.B 8 ++ [step7.q]) 9000000000000 (model7.caps 8) (model7.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded7_9 : ExcludedOn (model7.B 9 ++ [step7.q]) 9000000000000 (model7.caps 9) (model7.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked7 : StepValid model7 9000000000000 step7 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded7_1
    · exact excluded7_2
    · exact excluded7_3
    · exact excluded7_4
    · exact excluded7_5
    · exact excluded7_6
    · exact excluded7_7
    · exact excluded7_8
    · exact excluded7_9
theorem next7 : model7.insert step7 = model8 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext150000160000
end ConwaySoifer.Simplified.Certificates
