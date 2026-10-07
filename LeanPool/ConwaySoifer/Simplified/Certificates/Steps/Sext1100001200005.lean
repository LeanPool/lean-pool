/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext110000120000
import Mathlib.Tactic.FinCases

/-!
# Sext 110000 120000 5

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
namespace Sext110000120000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan40Owner2Part0 : FanWitness := (.next ([4920000000000], [1080000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([3495000000000], [795000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([3510000000000], [1500000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([3495000000000], [1875000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([3135000000000],
    [1860000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2430000000000], [1500000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([5115000000000, 9000000000000], [4380000000000,
    -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([1980000000000, 9000000000000],
    [2520000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([4125000000000],
    [5370000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([990000000000], [3510000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([990000000000, 9000000000000], [6000000000000, 0])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0], [1080000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([-90000000000, 9000000000000], [6000000000000, 0]) (some (0, 5, 3)) (some (0, 5, 4))
    (.next ([-1080000000000], [6000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-795000000000], [4290000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-1500000000000],
    [5010000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-1875000000000], [5370000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-1860000000000], [4995000000000]) (some (0, 5, 4))
    (some (5, 5, 4)) (.next ([-1500000000000], [3930000000000]) (some (5, 2, 4)) (some (5, 2, 4))
    (.next ([-4380000000000, 9000000000000], [9495000000000, 0]) (some (5, 2, 4)) (some (5, 2, 4))
    (.next ([-2520000000000, 9000000000000], [4500000000000, 0]) (some (5, 2, 4)) (some (5, 2, 4))
    (.next ([-5370000000000], [9495000000000]) (some (5, 2, 4)) (some (5, 3, 4)) (.next
    ([-3510000000000], [4500000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-6000000000000,
    0], [6990000000000, 9000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.terminal (some (5, 3,
    4)) (some (5, 3, 0)) (some (5, 3, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan41Owner0Part0 : FanWitness := (.next ([-177600000000, 2640000000000], [758400000000,
    2640000000000]) (some (8, 4, 5)) (some (8, 4, 5)) (.next ([-2385000000000], [9255000000000])
    (some (8, 4, 5)) (some (8, 4, 5)) (.next ([-2385000000000], [7995000000000]) (some (8, 4, 5))
    (some (8, 4, 5)) (.next ([-3045000000000], [9915000000000]) (some (8, 4, 5)) (some (8, 4, 5))
    (.next ([-660000000000], [1920000000000]) (some (8, 4, 5)) (some (8, 4, 5)) (.next
    ([-112800000000, -5280000000000], [290400000000, 2640000000000]) (some (8, 4, 5)) (some (8, 4,
    5)) (.next ([-3834600000000, 2640000000000], [5405400000000, 2640000000000]) (some (8, 4, 5))
    (some (8, 4, 7)) (.next ([-758400000000, -2640000000000], [1048800000000, 5280000000000]) (some
    (8, 4, 7)) (some (8, 4, 7)) (.next ([-4125000000000], [5583000000000]) (some (8, 4, 7)) (some
    (8, 4, 7)) (.next ([-5094600000000, 2640000000000], [6665400000000, 2640000000000]) (some (8, 4,
    7)) (some (8, 4, 7)) (.next ([-4415400000000, -2640000000000], [5695800000000, 5280000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-5385000000000], [6843000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([-5675400000000, -2640000000000], [6955800000000, 5280000000000]) (some
    (8, 4, 7)) (some (8, 4, 7)) (.next ([-5754600000000, 2640000000000], [6665400000000,
    2640000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-4705800000000, -5280000000000],
    [5405400000000, 2640000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-6045000000000],
    [6843000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-5965800000000, -5280000000000],
    [6665400000000, 2640000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-6335400000000,
    -2640000000000], [6955800000000, 5280000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
    ([-4415400000000, -2640000000000], [4824600000000, -2640000000000]) (some (8, 4, 7)) (some (8,
    4, 7)) (.next ([-5675400000000, -2640000000000], [6084600000000, -2640000000000]) (some (8, 4,
    7)) (some (8, 4, 7)) (.next ([-3084600000000, 2640000000000], [3289200000000, -5280000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-3955800000000, -5280000000000], [4160400000000,
    2640000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-3843000000000], [3870000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-6625800000000, -5280000000000], [6665400000000,
    2640000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.terminal (some (8, 4, 7)) (some (8, 4, 7))
    (some (8, 4, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan41Owner0Part1 : FanWitness := (.next ([6870000000000], [3045000000000]) (some (8, 3, 4))
    (some (8, 3, 4)) (.next ([1260000000000], [660000000000]) (some (8, 3, 4)) (some (8, 3, 4))
    (.next ([177600000000, -2640000000000], [112800000000, 5280000000000]) (some (8, 3, 4)) (some
    (8, 3, 4)) (.next ([1570800000000, 5280000000000], [3834600000000, -2640000000000]) (some (8, 3,
    4)) (some (8, 3, 4)) (.next ([290400000000, 2640000000000], [758400000000, 2640000000000]) (some
    (8, 3, 4)) (some (8, 3, 4)) (.next ([1458000000000], [4125000000000]) (some (8, 3, 4)) (some (8,
    3, 4)) (.next ([1570800000000, 5280000000000], [5094600000000, -2640000000000]) (some (8, 3, 4))
    (some (8, 3, 4)) (.next ([1280400000000, 2640000000000], [4415400000000, 2640000000000]) (some
    (8, 3, 4)) (some (8, 3, 4)) (.next ([1458000000000], [5385000000000]) (some (8, 3, 4)) (some (8,
    3, 4)) (.next ([1280400000000, 2640000000000], [5675400000000, 2640000000000]) (some (8, 3, 4))
    (some (8, 3, 4)) (.next ([910800000000, 5280000000000], [5754600000000, -2640000000000]) (some
    (8, 3, 4)) (some (8, 3, 4)) (.next ([699600000000, -2640000000000], [4705800000000,
    5280000000000]) (some (8, 3, 4)) (some (8, 3, 5)) (.next ([798000000000], [6045000000000]) (some
    (8, 3, 5)) (some (8, 3, 5)) (.next ([699600000000, -2640000000000], [5965800000000,
    5280000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([620400000000, 2640000000000],
    [6335400000000, 2640000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([409200000000,
    -5280000000000], [4415400000000, 2640000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next
    ([409200000000, -5280000000000], [5675400000000, 2640000000000]) (some (8, 3, 5)) (some (8, 3,
    5)) (.next ([204600000000, -2640000000000], [3084600000000, -2640000000000]) (some (8, 3, 5))
    (some (8, 3, 5)) (.next ([204600000000, -2640000000000], [3955800000000, 5280000000000]) (some
    (8, 3, 5)) (some (8, 3, 5)) (.next ([27000000000], [3843000000000]) (some (8, 3, 5)) (some (8,
    3, 5)) (.next ([39600000000, -2640000000000], [6625800000000, 5280000000000]) (some (8, 3, 5))
    (some (8, 3, 5)) (.next ([0, 0], [871200000000, 7920000000000]) (some (8, 3, 5)) (some (8, 3,
    5)) (.next ([-85800000000, -5280000000000], [3665400000000, 2640000000000]) (some (8, 3, 5))
    (some (8, 4, 5)) (.next ([-250800000000, -5280000000000], [6335400000000, 2640000000000]) (some
    (8, 4, 5)) (some (8, 4, 5)) fan41Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan41Owner3Part0 : FanWitness := (.next ([1365000000000, 9000000000000], [3675000000000,
    -9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([990000000000, 9000000000000],
    [6000000000000]) (some (5, 6, 3)) (some (5, 6, 4)) (.next ([495000000000], [4875000000000])
    (some (5, 6, 4)) (some (5, 6, 4)) (.next ([375000000000], [4665000000000]) (some (5, 6, 4))
    (some (5, 6, 4)) (.next ([330000000000, 9000000000000], [6000000000000]) (some (5, 6, 4)) (some
    (5, 6, 4)) (.next ([0], [660000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
    ([-255000000000], [3135000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-660000000000],
    [6000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-630000000000], [5505000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-630000000000], [4845000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-465000000000], [3465000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-960000000000], [5625000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-960000000000], [4965000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1965000000000],
    [4470000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-4140000000000, 9000000000000],
    [8505000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2625000000000], [5130000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-5130000000000], [8505000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-210000000000], [330000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-3885000000000, 9000000000000], [5370000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-3675000000000, 9000000000000], [5040000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-6000000000000, 0], [6990000000000, 9000000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-4875000000000], [5370000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-4665000000000], [5040000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-6000000000000,
    0], [6330000000000, 9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.terminal (some (0, 6,
    4)) (some (0, 6, 4)) (some (0, 6, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan44Owner2Part0 : FanWitness := (.next ([1485000000000], [4125000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([1350000000000], [3765000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([990000000000], [4260000000000]) (some (0, 2, 4)) (some (0, 6, 4)) (.next
    ([900000000000], [4140000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([990000000000,
    9000000000000], [6000000000000, 0]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([0],
    [1080000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-90000000000, 9000000000000],
    [6000000000000, 0]) (some (0, 6, 4)) (some (0, 6, 5)) (.next ([-750000000000], [5010000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-1080000000000], [6000000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-960000000000], [5100000000000]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-750000000000], [3930000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-960000000000], [4020000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-4515000000000],
    [10125000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-4515000000000], [9045000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-120000000000], [210000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-3270000000000, 9000000000000], [5250000000000, 0]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-3150000000000, 9000000000000], [5040000000000, 0]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-3135000000000, 9000000000000], [4620000000000, -9000000000000]) (some
    (0, 6, 5)) (some (0, 6, 5)) (.next ([-3555000000000], [5025000000000]) (some (0, 6, 5)) (some
    (0, 6, 5)) (.next ([-4125000000000], [5610000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-3765000000000], [5115000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-4260000000000],
    [5250000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-4140000000000], [5040000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-6000000000000, 0], [6990000000000, 9000000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.terminal (some (0, 6, 5)) (some (0, 6, 0)) (some (0, 6,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan47Owner2Part0 : FanWitness := (.next ([1140000000000], [2970000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([990000000000], [4260000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([900000000000], [4140000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([990000000000, 9000000000000], [6000000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([90000000000], [1920000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([0], [1080000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-90000000000, 9000000000000], [6000000000000, 0])
    (some (0, 2, 4)) (some (0, 2, 5)) (.next ([-750000000000], [5010000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-1080000000000], [6000000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-960000000000], [5100000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-750000000000], [3930000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-960000000000],
    [4020000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2010000000000, 9000000000000],
    [8010000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-990000000000], [3000000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3000000000000], [8010000000000]) (some (0, 2, 5))
    (some (6, 2, 5)) (.next ([-120000000000], [210000000000]) (some (6, 2, 5)) (some (6, 2, 5))
    (.next ([-3270000000000, 9000000000000], [5250000000000, 0]) (some (6, 2, 5)) (some (6, 3, 5))
    (.next ([-3150000000000, 9000000000000], [5040000000000, 0]) (some (6, 3, 5)) (some (6, 3, 5))
    (.next ([-2760000000000], [4020000000000]) (some (6, 3, 5)) (some (6, 4, 5)) (.next
    ([-2970000000000], [4110000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-4260000000000],
    [5250000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-4140000000000], [5040000000000])
    (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-6000000000000, 0], [6990000000000, 9000000000000])
    (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-1920000000000], [2010000000000]) (some (6, 4, 5))
    (some (6, 4, 5)) (.terminal (some (6, 4, 5)) (some (6, 4, 0)) (some (6, 4,
    5)))))))))))))))))))))))))))

theorem excluded40_0 : ExcludedOn (model40.B 0 ++ [step40.q]) 9000000000000 (model40.caps 0)
    (model40.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_1 : ExcludedOn (model40.B 1 ++ [step40.q]) 9000000000000 (model40.caps 1)
    (model40.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_2 : ExcludedOn (model40.B 2 ++ [step40.q]) 9000000000000 (model40.caps 2)
    (model40.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5910000000000, 9000000000000], [90000000000,
      -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) fan40Owner2Part0)) (den := 9000000000000)
      (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_4 : ExcludedOn (model40.B 4 ++ [step40.q]) 9000000000000 (model40.caps 4)
    (model40.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_5 : ExcludedOn (model40.B 5 ++ [step40.q]) 9000000000000 (model40.caps 5)
    (model40.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_6 : ExcludedOn (model40.B 6 ++ [step40.q]) 9000000000000 (model40.caps 6)
    (model40.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded40_4
    · exact excluded40_5
    · exact excluded40_6
    · exact excluded40_7
    · exact excluded40_8
    · exact excluded40_9
theorem next40 : model40.insert step40 = model41 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded41_0 : ExcludedOn (model41.B 0 ++ [step41.q]) 9000000000000 (model41.caps 0)
    (model41.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3579600000000, -2640000000000], [85800000000,
      5280000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([6084600000000, -2640000000000],
      [250800000000, 5280000000000]) (some (7, 8, 4)) (some (8, 8, 4)) (.next ([580800000000,
      5280000000000], [177600000000, -2640000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next
      ([6870000000000], [2385000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next ([5610000000000],
      [2385000000000]) (some (8, 3, 4)) (some (8, 3, 4)) fan41Owner0Part1)))))) (den :=
      9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded41_1 : ExcludedOn (model41.B 1 ++ [step41.q]) 9000000000000 (model41.caps 1)
    (model41.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_2 : ExcludedOn (model41.B 2 ++ [step41.q]) 9000000000000 (model41.caps 2)
    (model41.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_3 : ExcludedOn (model41.B 3 ++ [step41.q]) 9000000000000 (model41.caps 3)
    (model41.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2880000000000], [255000000000]) (some (4, 0, 6))
      (some (5, 0, 6)) (.next ([5340000000000], [660000000000]) (some (5, 0, 2)) (some (5, 0, 2))
      (.next ([4875000000000], [630000000000]) (some (5, 0, 2)) (some (5, 0, 2)) (.next
      ([4215000000000], [630000000000]) (some (5, 0, 2)) (some (5, 0, 2)) (.next ([3000000000000],
      [465000000000]) (some (5, 0, 2)) (some (5, 0, 2)) (.next ([4665000000000], [960000000000])
      (some (5, 0, 2)) (some (5, 0, 2)) (.next ([4005000000000], [960000000000]) (some (5, 0, 2))
      (some (5, 0, 2)) (.next ([2505000000000], [1965000000000]) (some (5, 0, 2)) (some (5, 0, 2))
      (.next ([4365000000000, 9000000000000], [4140000000000, -9000000000000]) (some (5, 0, 2))
      (some (5, 0, 2)) (.next ([2505000000000], [2625000000000]) (some (5, 0, 2)) (some (5, 0, 2))
      (.next ([3375000000000], [5130000000000]) (some (5, 0, 2)) (some (5, 6, 2)) (.next
      ([120000000000], [210000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([1485000000000,
      9000000000000], [3885000000000, -9000000000000]) (some (5, 6, 2)) (some (5, 6, 3))
      fan41Owner3Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded41_5 : ExcludedOn (model41.B 5 ++ [step41.q]) 9000000000000 (model41.caps 5)
    (model41.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_6 : ExcludedOn (model41.B 6 ++ [step41.q]) 9000000000000 (model41.caps 6)
    (model41.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_1 : ExcludedOn (model42.B 1 ++ [step42.q]) 9000000000000 (model42.caps 1)
    (model42.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5730000000000, 9000000000000], [4260000000000,
      -9000000000000]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([990000000000, 9000000000000],
      [990000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([4740000000000],
      [5250000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([3750000000000, -9000000000000],
      [5250000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [990000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-4260000000000, 9000000000000],
      [9990000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-990000000000, -9000000000000],
      [1980000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-5250000000000],
      [9990000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-5250000000000, 0],
      [9000000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1, 0))
      (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded42_3 : ExcludedOn (model42.B 3 ++ [step42.q]) 9000000000000 (model42.caps 3)
    (model42.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_4 : ExcludedOn (model42.B 4 ++ [step42.q]) 9000000000000 (model42.caps 4)
    (model42.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_5 : ExcludedOn (model42.B 5 ++ [step42.q]) 9000000000000 (model42.caps 5)
    (model42.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_6 : ExcludedOn (model42.B 6 ++ [step42.q]) 9000000000000 (model42.caps 6)
    (model42.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded42_3
    · exact excluded42_4
    · exact excluded42_5
    · exact excluded42_6
    · exact excluded42_7
    · exact excluded42_8
    · exact excluded42_9
theorem next42 : model42.insert step42 = model43 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded43_0 : ExcludedOn (model43.B 0 ++ [step43.q]) 9000000000000 (model43.caps 0)
    (model43.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_1 : ExcludedOn (model43.B 1 ++ [step43.q]) 9000000000000 (model43.caps 1)
    (model43.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5850000000000, 9000000000000], [4050000000000,
      -9000000000000]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([990000000000, 9000000000000],
      [990000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([4860000000000],
      [5040000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([3870000000000, -9000000000000],
      [5040000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [990000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-4050000000000, 9000000000000],
      [9900000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-990000000000, -9000000000000],
      [1980000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-5040000000000],
      [9900000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-5040000000000, 0],
      [8910000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1, 0))
      (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded43_3 : ExcludedOn (model43.B 3 ++ [step43.q]) 9000000000000 (model43.caps 3)
    (model43.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_4 : ExcludedOn (model43.B 4 ++ [step43.q]) 9000000000000 (model43.caps 4)
    (model43.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_5 : ExcludedOn (model43.B 5 ++ [step43.q]) 9000000000000 (model43.caps 5)
    (model43.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_6 : ExcludedOn (model43.B 6 ++ [step43.q]) 9000000000000 (model43.caps 6)
    (model43.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked43 : StepValid model43 9000000000000 step43 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded43_0
    · exact excluded43_1
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_2 : ExcludedOn (model44.B 2 ++ [step44.q]) 9000000000000 (model44.caps 2)
    (model44.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5910000000000, 9000000000000], [90000000000,
      -9000000000000]) (some (0, 0, 6)) (some (0, 1, 6)) (.next ([4260000000000], [750000000000])
      (some (0, 1, 6)) (some (0, 1, 6)) (.next ([4920000000000], [1080000000000]) (some (0, 1, 6))
      (some (0, 1, 6)) (.next ([4140000000000], [960000000000]) (some (0, 1, 6)) (some (0, 1, 6))
      (.next ([3180000000000], [750000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
      ([3060000000000], [960000000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next ([5610000000000],
      [4515000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([4530000000000], [4515000000000])
      (some (0, 2, 6)) (some (0, 2, 6)) (.next ([90000000000], [120000000000]) (some (0, 2, 6))
      (some (0, 2, 6)) (.next ([1980000000000, 9000000000000], [3270000000000, -9000000000000])
      (some (0, 2, 6)) (some (0, 2, 6)) (.next ([1890000000000, 9000000000000], [3150000000000,
      -9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([1485000000000, 0], [3135000000000,
      -9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([1470000000000], [3555000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) fan44Owner2Part0)))))))))))))) (den := 9000000000000) (fuel
      := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded44_3 : ExcludedOn (model44.B 3 ++ [step44.q]) 9000000000000 (model44.caps 3)
    (model44.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_4 : ExcludedOn (model44.B 4 ++ [step44.q]) 9000000000000 (model44.caps 4)
    (model44.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_5 : ExcludedOn (model44.B 5 ++ [step44.q]) 9000000000000 (model44.caps 5)
    (model44.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_6 : ExcludedOn (model44.B 6 ++ [step44.q]) 9000000000000 (model44.caps 6)
    (model44.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_7 : ExcludedOn (model44.B 7 ++ [step44.q]) 9000000000000 (model44.caps 7)
    (model44.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_8 : ExcludedOn (model44.B 8 ++ [step44.q]) 9000000000000 (model44.caps 8)
    (model44.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_9 : ExcludedOn (model44.B 9 ++ [step44.q]) 9000000000000 (model44.caps 9)
    (model44.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked44 : StepValid model44 9000000000000 step44 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded44_0
    · exact (hj rfl).elim
    · exact excluded44_2
    · exact excluded44_3
    · exact excluded44_4
    · exact excluded44_5
    · exact excluded44_6
    · exact excluded44_7
    · exact excluded44_8
    · exact excluded44_9
theorem next44 : model44.insert step44 = model45 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded45_1 : ExcludedOn (model45.B 1 ++ [step45.q]) 9000000000000 (model45.caps 1)
    (model45.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_2 : ExcludedOn (model45.B 2 ++ [step45.q]) 9000000000000 (model45.caps 2)
    (model45.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_3 : ExcludedOn (model45.B 3 ++ [step45.q]) 9000000000000 (model45.caps 3)
    (model45.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_4 : ExcludedOn (model45.B 4 ++ [step45.q]) 9000000000000 (model45.caps 4)
    (model45.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_5 : ExcludedOn (model45.B 5 ++ [step45.q]) 9000000000000 (model45.caps 5)
    (model45.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8208000000000], [792000000000]) (some (4, 0, 4))
      (some (4, 1, 4)) (.next ([8208000000000, 9000000000000], [1167000000000, -9000000000000])
      (some (3, 1, 4)) (some (3, 1, 4)) (.next ([7218000000000], [2157000000000]) (some (3, 1, 4))
      (some (3, 1, 4)) (.next ([375000000000], [990000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([1365000000000], [6750000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([990000000000, 9000000000000], [7125000000000, 0]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([93000000000], [2157000000000]) (some (3, 1, 4)) (some (0, 1, 4)) (.next ([0, 0],
      [990000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-792000000000],
      [9000000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1167000000000, 9000000000000],
      [9375000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2157000000000],
      [9375000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-990000000000], [1365000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-6750000000000], [8115000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-7125000000000, 0], [8115000000000, 9000000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2157000000000], [2250000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.terminal (some (0, 2, 4)) (some (0, 4, 4)) (some (0, 4, 4))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded45_6 : ExcludedOn (model45.B 6 ++ [step45.q]) 9000000000000 (model45.caps 6)
    (model45.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1365000000000, 9000000000000], [792000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([1782000000000], [5853000000000,
      -9000000000000]) (some (2, 0, 2)) (some (2, 0, 2)) (.next ([375000000000], [1782000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([990000000000, 9000000000000], [8010000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [990000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-792000000000, 9000000000000],
      [2157000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-5853000000000, 9000000000000],
      [7635000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1782000000000],
      [2157000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-8010000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked45 : StepValid model45 9000000000000 step45 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded45_1
    · exact excluded45_2
    · exact excluded45_3
    · exact excluded45_4
    · exact excluded45_5
    · exact excluded45_6
    · exact excluded45_7
    · exact excluded45_8
    · exact excluded45_9
theorem next45 : model45.insert step45 = model46 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded46_0 : ExcludedOn (model46.B 0 ++ [step46.q]) 9000000000000 (model46.caps 0)
    (model46.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_1 : ExcludedOn (model46.B 1 ++ [step46.q]) 9000000000000 (model46.caps 1)
    (model46.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_2 : ExcludedOn (model46.B 2 ++ [step46.q]) 9000000000000 (model46.caps 2)
    (model46.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_4 : ExcludedOn (model46.B 4 ++ [step46.q]) 9000000000000 (model46.caps 4)
    (model46.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5130000000000], [495000000000]) (some (4, 0, 1))
      (some (4, 1, 1)) (.next ([5625000000000], [870000000000]) (some (4, 1, 1)) (some (4, 1, 1))
      (.next ([2505000000000], [1635000000000]) (some (4, 1, 1)) (some (4, 1, 2)) (.next
      ([3990000000000], [5010000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([990000000000],
      [2010000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([990000000000],
      [3000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([990000000000, 9000000000000],
      [6000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([495000000000, 9000000000000],
      [4635000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [6000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-495000000000], [5625000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-870000000000], [6495000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-1635000000000], [4140000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-5010000000000], [9000000000000]) (some (0, 1, 2)) (some (0, 1, 4)) (.next
      ([-2010000000000, 9000000000000], [3000000000000, -9000000000000]) (some (0, 1, 4)) (some (0,
      1, 4)) (.next ([-3000000000000], [3990000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-6000000000000], [6990000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-4635000000000, 9000000000000], [5130000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.terminal (some (0, 1, 4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded46_5 : ExcludedOn (model46.B 5 ++ [step46.q]) 9000000000000 (model46.caps 5)
    (model46.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_6 : ExcludedOn (model46.B 6 ++ [step46.q]) 9000000000000 (model46.caps 6)
    (model46.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_7 : ExcludedOn (model46.B 7 ++ [step46.q]) 9000000000000 (model46.caps 7)
    (model46.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_8 : ExcludedOn (model46.B 8 ++ [step46.q]) 9000000000000 (model46.caps 8)
    (model46.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6000000000000], [3990000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([2550000000000], [3450000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([585000000000], [5955000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([45000000000], [3990000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [5955000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.next ([-3990000000000], [9990000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-3450000000000], [6000000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-5955000000000], [6540000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-3990000000000], [4035000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded46_9 : ExcludedOn (model46.B 9 ++ [step46.q]) 9000000000000 (model46.caps 9)
    (model46.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded46_1
    · exact excluded46_2
    · exact (hj rfl).elim
    · exact excluded46_4
    · exact excluded46_5
    · exact excluded46_6
    · exact excluded46_7
    · exact excluded46_8
    · exact excluded46_9
theorem next46 : model46.insert step46 = model47 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded47_0 : ExcludedOn (model47.B 0 ++ [step47.q]) 9000000000000 (model47.caps 0)
    (model47.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_1 : ExcludedOn (model47.B 1 ++ [step47.q]) 9000000000000 (model47.caps 1)
    (model47.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_2 : ExcludedOn (model47.B 2 ++ [step47.q]) 9000000000000 (model47.caps 2)
    (model47.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5910000000000, 9000000000000], [90000000000,
      -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([4260000000000], [750000000000])
      (some (0, 6, 4)) (some (0, 6, 4)) (.next ([4920000000000], [1080000000000]) (some (0, 6, 4))
      (some (0, 6, 4)) (.next ([4140000000000], [960000000000]) (some (0, 6, 4)) (some (0, 6, 4))
      (.next ([3180000000000], [750000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
      ([3060000000000], [960000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([6000000000000,
      9000000000000], [2010000000000, -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
      ([2010000000000], [990000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([5010000000000],
      [3000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([90000000000], [120000000000])
      (some (0, 6, 4)) (some (0, 6, 4)) (.next ([1980000000000, 9000000000000], [3270000000000,
      -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([1890000000000, 9000000000000],
      [3150000000000, -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([1260000000000],
      [2760000000000]) (some (0, 6, 4)) (some (0, 6, 4)) fan47Owner2Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded47_4 : ExcludedOn (model47.B 4 ++ [step47.q]) 9000000000000 (model47.caps 4)
    (model47.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_5 : ExcludedOn (model47.B 5 ++ [step47.q]) 9000000000000 (model47.caps 5)
    (model47.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_6 : ExcludedOn (model47.B 6 ++ [step47.q]) 9000000000000 (model47.caps 6)
    (model47.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_7 : ExcludedOn (model47.B 7 ++ [step47.q]) 9000000000000 (model47.caps 7)
    (model47.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_8 : ExcludedOn (model47.B 8 ++ [step47.q]) 9000000000000 (model47.caps 8)
    (model47.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_9 : ExcludedOn (model47.B 9 ++ [step47.q]) 9000000000000 (model47.caps 9)
    (model47.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked47 : StepValid model47 9000000000000 step47 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded47_0
    · exact excluded47_1
    · exact excluded47_2
    · exact (hj rfl).elim
    · exact excluded47_4
    · exact excluded47_5
    · exact excluded47_6
    · exact excluded47_7
    · exact excluded47_8
    · exact excluded47_9
theorem next47 : model47.insert step47 = model48 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext110000120000
end ConwaySoifer.Simplified.Certificates
