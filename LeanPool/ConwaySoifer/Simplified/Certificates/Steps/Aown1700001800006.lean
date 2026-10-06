/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown170000180000
import Mathlib.Tactic.FinCases

/-!
# Aown 170000 180000 6

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
namespace Aown170000180000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner0Part0 : FanWitness := (.next ([-4755000000000], [8010000000000]) (some (1, 5, 9))
    (some (1, 5, 9)) (.next ([-255000000000], [420000000000]) (some (1, 5, 9)) (some (1, 5, 9))
    (.next ([-4965000000000], [8010000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next
    ([-5100000000000], [8010000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-5145000000000],
    [7635000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-5130000000000], [7500000000000])
    (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-1410000000000], [2025000000000]) (some (1, 5, 9))
    (some (1, 5, 9)) (.next ([-5490000000000], [7635000000000]) (some (1, 5, 9)) (some (1, 5, 9))
    (.next ([-5475000000000], [7500000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next
    ([-1530000000000], [2010000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-4995000000000],
    [6390000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-5610000000000], [6870000000000])
    (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-5745000000000], [7005000000000]) (some (1, 5, 9))
    (some (1, 5, 9)) (.next ([-6495000000000], [7380000000000]) (some (1, 5, 9)) (some (1, 5, 9))
    (.next ([-6600000000000], [7395000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next
    ([-3495000000000], [3915000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-6630000000000],
    [7380000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-3840000000000], [4260000000000])
    (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-1275000000000], [1410000000000]) (some (1, 5, 9))
    (some (1, 5, 9)) (.next ([-3240000000000], [3495000000000]) (some (1, 5, 9)) (some (1, 5, 9))
    (.next ([-3585000000000], [3840000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next
    ([-6765000000000], [7140000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-7080000000000],
    [7260000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-7215000000000], [7260000000000])
    (some (1, 5, 9)) (some (1, 5, 9)) (.terminal (some (1, 5, 9)) (some (1, 5, 9)) (some (1, 5,
    9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner0Part1 : FanWitness := (.next ([-1125000000000], [7755000000000]) (some (11, 3, 8))
    (some (11, 4, 8)) (.next ([-1260000000000], [7755000000000]) (some (11, 4, 8)) (some (11, 4, 8))
    (.next ([-1230000000000], [7215000000000]) (some (11, 4, 8)) (some (11, 4, 8)) (.next
    ([-1215000000000], [7080000000000]) (some (11, 4, 8)) (some (11, 4, 8)) (.next ([-135000000000],
    [750000000000]) (some (11, 4, 8)) (some (11, 5, 8)) (.next ([-135000000000], [615000000000])
    (some (0, 5, 8)) (some (0, 5, 8)) (.next ([-1650000000000], [7380000000000]) (some (0, 5, 8))
    (some (0, 5, 8)) (.next ([-1635000000000], [7245000000000]) (some (0, 5, 8)) (some (0, 5, 8))
    (.next ([-630000000000], [2505000000000]) (some (0, 5, 8)) (some (0, 5, 8)) (.next
    ([-630000000000], [2160000000000]) (some (0, 5, 8)) (some (0, 5, 8)) (.next ([-510000000000],
    [1500000000000]) (some (0, 5, 8)) (some (0, 5, 9)) (.next ([-645000000000], [1635000000000])
    (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-375000000000], [900000000000]) (some (0, 5, 9))
    (some (0, 5, 9)) (.next ([-375000000000], [885000000000]) (some (0, 5, 9)) (some (0, 5, 9))
    (.next ([-3120000000000], [7020000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next
    ([-375000000000], [765000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-3465000000000],
    [7020000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-3735000000000], [7500000000000])
    (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-375000000000], [750000000000]) (some (0, 5, 9))
    (some (0, 5, 9)) (.next ([-3870000000000], [7635000000000]) (some (0, 5, 9)) (some (1, 5, 9))
    (.next ([-4080000000000], [7500000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next
    ([-4215000000000], [7635000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-510000000000],
    [885000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-4620000000000], [8010000000000])
    (some (1, 5, 9)) (some (1, 5, 9)) fan48Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner0Part2 : FanWitness := (.next ([1260000000000], [5610000000000]) (some (9, 3, 6))
    (some (11, 3, 6)) (.next ([1260000000000], [5745000000000]) (some (11, 3, 6)) (some (11, 3, 6))
    (.next ([885000000000], [6495000000000]) (some (11, 3, 6)) (some (11, 3, 6)) (.next
    ([795000000000], [6600000000000]) (some (11, 3, 6)) (some (11, 3, 6)) (.next ([420000000000],
    [3495000000000]) (some (11, 3, 6)) (some (11, 3, 6)) (.next ([750000000000], [6630000000000])
    (some (11, 3, 6)) (some (11, 3, 6)) (.next ([420000000000], [3840000000000]) (some (11, 3, 6))
    (some (11, 3, 6)) (.next ([135000000000], [1275000000000]) (some (11, 3, 6)) (some (11, 3, 6))
    (.next ([255000000000], [3240000000000]) (some (11, 3, 6)) (some (11, 3, 6)) (.next
    ([255000000000], [3585000000000]) (some (11, 3, 6)) (some (11, 3, 7)) (.next ([375000000000],
    [6765000000000]) (some (11, 3, 7)) (some (11, 3, 7)) (.next ([180000000000], [7080000000000])
    (some (11, 3, 7)) (some (11, 3, 7)) (.next ([45000000000], [7215000000000]) (some (11, 3, 7))
    (some (11, 3, 7)) (.next ([0], [1275000000000]) (some (11, 3, 7)) (some (11, 3, 7)) (.next
    ([-15000000000], [7020000000000]) (some (11, 3, 7)) (some (11, 3, 8)) (.next ([-135000000000],
    [7005000000000]) (some (11, 3, 8)) (some (11, 3, 8)) (.next ([-240000000000], [7245000000000])
    (some (11, 3, 8)) (some (11, 3, 8)) (.next ([-210000000000], [6000000000000]) (some (11, 3, 8))
    (some (11, 3, 8)) (.next ([-375000000000], [7380000000000]) (some (11, 3, 8)) (some (11, 3, 8))
    (.next ([-375000000000], [5745000000000]) (some (11, 3, 8)) (some (11, 3, 8)) (.next
    ([-705000000000], [7590000000000]) (some (11, 3, 8)) (some (11, 3, 8)) (.next ([-135000000000],
    [1395000000000]) (some (11, 3, 8)) (some (11, 3, 8)) (.next ([-840000000000], [7590000000000])
    (some (11, 3, 8)) (some (11, 3, 8)) (.next ([-15000000000], [135000000000]) (some (11, 3, 8))
    (some (11, 3, 8)) fan48Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner0Part3 : FanWitness := (.next ([990000000000], [645000000000]) (some (9, 2, 5)) (some
    (9, 2, 5)) (.next ([525000000000], [375000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next
    ([510000000000], [375000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next ([3900000000000],
    [3120000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next ([390000000000], [375000000000]) (some
    (9, 2, 5)) (some (9, 2, 5)) (.next ([3555000000000], [3465000000000]) (some (9, 2, 5)) (some (9,
    3, 5)) (.next ([3765000000000], [3735000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([375000000000], [375000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([3765000000000],
    [3870000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([3420000000000], [4080000000000])
    (some (9, 3, 5)) (some (9, 3, 5)) (.next ([3420000000000], [4215000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([375000000000], [510000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    (.next ([3390000000000], [4620000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([3255000000000], [4755000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([165000000000],
    [255000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([3045000000000], [4965000000000])
    (some (9, 3, 5)) (some (9, 3, 6)) (.next ([2910000000000], [5100000000000]) (some (9, 3, 6))
    (some (9, 3, 6)) (.next ([2490000000000], [5145000000000]) (some (9, 3, 6)) (some (9, 3, 6))
    (.next ([2370000000000], [5130000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next
    ([615000000000], [1410000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([2145000000000],
    [5490000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([2025000000000], [5475000000000])
    (some (9, 3, 6)) (some (9, 3, 6)) (.next ([480000000000], [1530000000000]) (some (9, 3, 6))
    (some (9, 3, 6)) (.next ([1395000000000], [4995000000000]) (some (9, 3, 6)) (some (9, 3, 6))
    fan48Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner2Part0 : FanWitness := (.next ([510000000000], [1254000000000]) (some (0, 6, 3)) (some
    (0, 6, 3)) (.next ([1020000000000], [6855000000000]) (some (0, 6, 3)) (some (0, 6, 4)) (.next
    ([1020000000000], [7875000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([765000000000],
    [7110000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([510000000000], [7125000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([15000000000], [240000000000]) (some (0, 6, 4)) (some
    (0, 6, 4)) (.next ([0, 0], [1530000000000, 9000000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-240000000000], [8385000000000]) (some (0, 1, 4)) (some (0, 2, 5)) (.next
    ([-405000000000, -9000000000000], [8895000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-510000000000, -9000000000000], [8385000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2,
    5)) (.next ([-510000000000, -9000000000000], [7875000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-765000000000, -9000000000000], [8640000000000, 9000000000000]) (some (0, 2, 5)) (some
    (6, 2, 5)) (.next ([-1020000000000, -9000000000000], [8655000000000, 9000000000000]) (some (6,
    2, 5)) (some (6, 2, 5)) (.next ([-1530000000000, -9000000000000], [9000000000000, 0]) (some (6,
    2, 5)) (some (6, 2, 5)) (.next ([-1530000000000, -9000000000000], [7401000000000,
    9000000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-2004000000000], [8895000000000])
    (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-165000000000, -9000000000000], [510000000000, 0])
    (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-405000000000, -9000000000000], [765000000000, 0])
    (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-1254000000000], [1764000000000]) (some (6, 2, 5))
    (some (6, 2, 5)) (.next ([-6855000000000], [7875000000000]) (some (6, 2, 5)) (some (6, 2, 5))
    (.next ([-7875000000000], [8895000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next
    ([-7110000000000], [7875000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-7125000000000],
    [7635000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-240000000000], [255000000000])
    (some (6, 2, 5)) (some (6, 2, 5)) (.terminal (some (6, 2, 5)) (some (6, 3, 0)) (some (6, 3,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner4Part0 : FanWitness := (.next ([7980000000000], [1125000000000]) (some (3, 1, 5))
    (some (3, 1, 5)) (.next ([2805000000000], [750000000000]) (some (3, 1, 5)) (some (3, 1, 5))
    (.next ([6246000000000], [2544000000000]) (some (3, 1, 5)) (some (3, 1, 5)) (.next
    ([4500000000000], [2859000000000]) (some (3, 1, 5)) (some (3, 1, 5)) (.next ([4815000000000],
    [4290000000000]) (some (3, 1, 5)) (some (3, 1, 5)) (.next ([2010000000000], [3540000000000])
    (some (3, 1, 5)) (some (3, 1, 5)) (.next ([1530000000000, 9000000000000], [3165000000000]) (some
    (3, 1, 5)) (some (3, 1, 5)) (.next ([1155000000000, 9000000000000], [4020000000000,
    -9000000000000]) (some (3, 1, 5)) (some (3, 1, 5)) (.next ([621000000000], [4095000000000,
    -9000000000000]) (some (3, 1, 5)) (some (3, 1, 5)) (.next ([621000000000], [5625000000000])
    (some (3, 1, 5)) (some (4, 1, 5)) (.next ([405000000000, 9000000000000], [7575000000000,
    -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0], [3165000000000]) (some (4, 1,
    5)) (some (4, 1, 5)) (.next ([-375000000000], [5550000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-1125000000000], [9105000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-750000000000], [3555000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2544000000000],
    [8790000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2859000000000], [7359000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4290000000000], [9105000000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([-3540000000000], [5550000000000]) (some (0, 1, 3)) (some (0, 5, 3))
    (.next ([-3165000000000], [4695000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-4020000000000, 9000000000000], [5175000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-4095000000000, 9000000000000], [4716000000000, -9000000000000]) (some (0, 5, 3)) (some
    (0, 5, 3)) (.next ([-5625000000000], [6246000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-7575000000000, 9000000000000], [7980000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal
    (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

theorem excluded48_0 : ExcludedOn (model48.B 0 ++ [step48.q]) 9000000000000 (model48.caps 0)
    (model48.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7005000000000], [15000000000]) (some (9, 1, 5))
      (some (9, 2, 5)) (.next ([6870000000000], [135000000000]) (some (9, 2, 5)) (some (9, 2, 5))
      (.next ([7005000000000], [240000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next
      ([5790000000000], [210000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next ([7005000000000],
      [375000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next ([5370000000000], [375000000000])
      (some (9, 2, 5)) (some (9, 2, 5)) (.next ([6885000000000], [705000000000]) (some (9, 2, 5))
      (some (9, 2, 5)) (.next ([1260000000000], [135000000000]) (some (9, 2, 5)) (some (9, 2, 5))
      (.next ([6750000000000], [840000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next
      ([120000000000], [15000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next ([6630000000000],
      [1125000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next ([6495000000000], [1260000000000])
      (some (9, 2, 5)) (some (9, 2, 5)) (.next ([5985000000000], [1230000000000]) (some (9, 2, 5))
      (some (9, 2, 5)) (.next ([5865000000000], [1215000000000]) (some (9, 2, 5)) (some (9, 2, 5))
      (.next ([615000000000], [135000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next
      ([480000000000], [135000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next ([5730000000000],
      [1650000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next ([5610000000000], [1635000000000])
      (some (9, 2, 5)) (some (9, 2, 5)) (.next ([1875000000000], [630000000000]) (some (9, 2, 5))
      (some (9, 2, 5)) (.next ([1530000000000], [630000000000]) (some (9, 2, 5)) (some (9, 2, 5))
      (.next ([990000000000], [510000000000]) (some (9, 2, 5)) (some (9, 2, 5))
      fan48Owner0Part3))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded48_1 : ExcludedOn (model48.B 1 ++ [step48.q]) 9000000000000 (model48.caps 1)
    (model48.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_2 : ExcludedOn (model48.B 2 ++ [step48.q]) 9000000000000 (model48.caps 2)
    (model48.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8145000000000], [240000000000]) (some (0, 6, 3))
      (some (0, 6, 3)) (.next ([8490000000000, -9000000000000], [405000000000, 9000000000000]) (some
      (0, 6, 3)) (some (0, 6, 3)) (.next ([7875000000000, 0], [510000000000, 9000000000000]) (some
      (0, 6, 3)) (some (0, 6, 3)) (.next ([7365000000000, -9000000000000], [510000000000,
      9000000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([7875000000000, 0], [765000000000,
      9000000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([7635000000000, 0], [1020000000000,
      9000000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([7470000000000, -9000000000000],
      [1530000000000, 9000000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([5871000000000, 0],
      [1530000000000, 9000000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([6891000000000],
      [2004000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([345000000000, -9000000000000],
      [165000000000, 9000000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([360000000000,
      -9000000000000], [405000000000, 9000000000000]) (some (0, 6, 3)) (some (0, 6, 3))
      fan48Owner2Part0)))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded48_4 : ExcludedOn (model48.B 4 ++ [step48.q]) 9000000000000 (model48.caps 4)
    (model48.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5175000000000], [375000000000]) (some (3, 0, 5))
      (some (3, 1, 5)) fan48Owner4Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded48_5 : ExcludedOn (model48.B 5 ++ [step48.q]) 9000000000000 (model48.caps 5)
    (model48.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_6 : ExcludedOn (model48.B 6 ++ [step48.q]) 9000000000000 (model48.caps 6)
    (model48.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_7 : ExcludedOn (model48.B 7 ++ [step48.q]) 9000000000000 (model48.caps 7)
    (model48.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_8 : ExcludedOn (model48.B 8 ++ [step48.q]) 9000000000000 (model48.caps 8)
    (model48.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_9 : ExcludedOn (model48.B 9 ++ [step48.q]) 9000000000000 (model48.caps 9)
    (model48.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked48 : StepValid model48 9000000000000 step48 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded48_0
    · exact excluded48_1
    · exact excluded48_2
    · exact (hj rfl).elim
    · exact excluded48_4
    · exact excluded48_5
    · exact excluded48_6
    · exact excluded48_7
    · exact excluded48_8
    · exact excluded48_9
theorem next48 : model48.insert step48 = model49 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Aown170000180000
end ConwaySoifer.Simplified.Certificates
