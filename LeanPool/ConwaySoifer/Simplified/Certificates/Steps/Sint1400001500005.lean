/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint140000150000
import Mathlib.Tactic.FinCases

/-!
# Sint 140000 150000 5

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
def fan44Owner4Part0 : FanWitness := (.next ([1545000000000], [4335000000000]) (some (5, 6, 3))
    (some (5, 6, 4)) (.next ([840000000000], [3120000000000]) (some (5, 6, 4)) (some (5, 6, 4))
    (.next ([90000000000], [375000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([390000000000],
    [2235000000000]) (some (5, 6, 4)) (some (5, 6, 5)) (.next ([375000000000], [3960000000000])
    (some (5, 6, 5)) (some (5, 6, 5)) (.next ([375000000000], [5040000000000]) (some (5, 6, 5))
    (some (5, 6, 5)) (.next ([0, 0], [1260000000000, 9000000000000]) (some (5, 6, 5)) (some (5, 6,
    5)) (.next ([0, -9000000000000], [2625000000000, 0]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-885000000000, -9000000000000], [6300000000000, 9000000000000]) (some (0, 6, 5)) (some (0, 6,
    5)) (.next ([-1260000000000, -9000000000000], [6765000000000, 9000000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-885000000000, -9000000000000], [3960000000000, 0]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-3120000000000], [8535000000000]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-3495000000000], [9000000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-3510000000000], [6300000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-3885000000000],
    [6765000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-885000000000], [1335000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-2625000000000], [3885000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-3960000000000], [5415000000000]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-4335000000000], [5880000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-3120000000000], [3960000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-375000000000],
    [465000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-2235000000000], [2625000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-3960000000000], [4335000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([-5040000000000], [5415000000000]) (some (0, 3, 5)) (some (0, 3, 5))
    (.terminal (some (0, 3, 5)) (some (0, 3, 5)) (some (0, 3, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan45Owner0Part0 : FanWitness := (.next ([-840000000000], [5505000000000]) (some (8, 4, 6))
    (some (8, 4, 6)) (.next ([-1590000000000], [6750000000000]) (some (8, 4, 6)) (some (8, 4, 6))
    (.next ([-480000000000], [2010000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next
    ([-1680000000000], [6750000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-1590000000000],
    [5925000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-1680000000000], [5925000000000])
    (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-2010000000000], [6420000000000]) (some (8, 4, 6))
    (some (8, 4, 6)) (.next ([-2580000000000], [7950000000000]) (some (8, 4, 6)) (some (8, 4, 6))
    (.next ([-2955000000000], [8700000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next
    ([-2010000000000], [5595000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-3705000000000],
    [9120000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-3795000000000], [9120000000000])
    (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-330000000000], [750000000000]) (some (1, 4, 6))
    (some (1, 4, 6)) (.next ([-705000000000], [1545000000000]) (some (1, 4, 6)) (some (1, 4, 6))
    (.next ([-1305000000000], [2835000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next
    ([-4125000000000], [8790000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-1755000000000],
    [3645000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-375000000000], [750000000000])
    (some (1, 4, 6)) (some (1, 4, 8)) (.next ([-2115000000000], [3195000000000]) (some (1, 4, 8))
    (some (2, 5, 8)) (.next ([-6060000000000], [7125000000000]) (some (2, 5, 8)) (some (2, 5, 8))
    (.next ([-2115000000000], [2370000000000]) (some (2, 5, 8)) (some (2, 5, 8)) (.next
    ([-6810000000000], [7500000000000]) (some (2, 5, 8)) (some (2, 5, 8)) (.next ([-1080000000000],
    [1170000000000]) (some (2, 5, 8)) (some (2, 5, 8)) (.next ([-1125000000000], [1170000000000])
    (some (2, 5, 8)) (some (2, 5, 8)) (.terminal (some (2, 5, 8)) (some (2, 5, 8)) (some (2, 5,
    8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan45Owner0Part1 : FanWitness := (.next ([5745000000000], [2955000000000]) (some (8, 2, 6))
    (some (8, 2, 6)) (.next ([3585000000000], [2010000000000]) (some (8, 2, 6)) (some (8, 2, 6))
    (.next ([5415000000000], [3705000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next
    ([5325000000000], [3795000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([420000000000],
    [330000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([840000000000], [705000000000]) (some
    (8, 2, 6)) (some (8, 3, 6)) (.next ([1530000000000], [1305000000000]) (some (8, 3, 6)) (some (8,
    3, 6)) (.next ([4665000000000], [4125000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
    ([1890000000000], [1755000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([375000000000],
    [375000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([1080000000000], [2115000000000])
    (some (8, 3, 6)) (some (8, 3, 6)) (.next ([1065000000000], [6060000000000]) (some (8, 3, 6))
    (some (8, 3, 6)) (.next ([255000000000], [2115000000000]) (some (8, 3, 6)) (some (8, 3, 6))
    (.next ([690000000000], [6810000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
    ([90000000000], [1080000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([45000000000],
    [1125000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([0], [825000000000]) (some (8, 3, 6))
    (some (8, 3, 6)) (.next ([-60000000000], [7230000000000]) (some (8, 3, 6)) (some (8, 4, 6))
    (.next ([-150000000000], [7230000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next
    ([-45000000000], [1215000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-480000000000],
    [6900000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-465000000000], [5580000000000])
    (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-465000000000], [4755000000000]) (some (8, 4, 6))
    (some (8, 4, 6)) (.next ([-840000000000], [6330000000000]) (some (8, 4, 6)) (some (8, 4, 6))
    fan45Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan46Owner0Part0 : FanWitness := (.next ([-840000000000], [6330000000000]) (some (8, 4, 6))
    (some (8, 4, 6)) (.next ([-840000000000], [5505000000000]) (some (8, 4, 6)) (some (8, 4, 6))
    (.next ([-1590000000000], [6750000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next
    ([-480000000000], [2010000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-1680000000000],
    [6750000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-1590000000000], [5925000000000])
    (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-1680000000000], [5925000000000]) (some (8, 4, 6))
    (some (8, 4, 6)) (.next ([-2010000000000], [6420000000000]) (some (8, 4, 6)) (some (8, 4, 6))
    (.next ([-2010000000000], [5595000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next
    ([-330000000000], [750000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-705000000000],
    [1545000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-1305000000000], [2835000000000])
    (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-375000000000], [750000000000]) (some (8, 4, 6))
    (some (8, 4, 6)) (.next ([-6105000000000], [9525000000000]) (some (8, 4, 6)) (some (8, 5, 6))
    (.next ([-2355000000000], [3480000000000]) (some (8, 5, 6)) (some (8, 5, 6)) (.next
    ([-2445000000000], [3570000000000]) (some (8, 5, 6)) (some (8, 5, 6)) (.next ([-4800000000000],
    [6690000000000]) (some (8, 5, 6)) (some (8, 5, 6)) (.next ([-2025000000000], [2730000000000])
    (some (8, 5, 6)) (some (8, 5, 6)) (.next ([-5625000000000], [7515000000000]) (some (8, 5, 6))
    (some (8, 5, 6)) (.next ([-3105000000000], [3900000000000]) (some (8, 5, 6)) (some (8, 5, 6))
    (.next ([-6060000000000], [7125000000000]) (some (8, 5, 6)) (some (8, 5, 6)) (.next
    ([-6810000000000], [7500000000000]) (some (8, 5, 6)) (some (8, 5, 6)) (.next ([-1080000000000],
    [1170000000000]) (some (8, 5, 6)) (some (8, 5, 6)) (.next ([-1125000000000], [1170000000000])
    (some (8, 5, 6)) (some (8, 5, 6)) (.terminal (some (8, 5, 6)) (some (8, 5, 6)) (some (8, 5,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan46Owner0Part1 : FanWitness := (.next ([3585000000000], [2010000000000]) (some (7, 8, 6))
    (some (7, 8, 6)) (.next ([420000000000], [330000000000]) (some (7, 8, 6)) (some (7, 8, 6))
    (.next ([840000000000], [705000000000]) (some (7, 8, 6)) (some (7, 8, 6)) (.next
    ([1530000000000], [1305000000000]) (some (7, 8, 6)) (some (7, 8, 6)) (.next ([375000000000],
    [375000000000]) (some (7, 8, 6)) (some (7, 8, 6)) (.next ([3420000000000], [6105000000000])
    (some (7, 8, 6)) (some (7, 8, 6)) (.next ([1125000000000], [2355000000000]) (some (7, 8, 6))
    (some (7, 8, 6)) (.next ([1125000000000], [2445000000000]) (some (7, 3, 6)) (some (7, 3, 6))
    (.next ([1890000000000], [4800000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next
    ([705000000000], [2025000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([1890000000000],
    [5625000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([795000000000], [3105000000000])
    (some (7, 3, 6)) (some (8, 3, 6)) (.next ([1065000000000], [6060000000000]) (some (8, 3, 6))
    (some (8, 3, 6)) (.next ([690000000000], [6810000000000]) (some (8, 3, 6)) (some (8, 3, 6))
    (.next ([90000000000], [1080000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([45000000000],
    [1125000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([0], [825000000000]) (some (8, 3, 6))
    (some (8, 3, 6)) (.next ([-60000000000], [7230000000000]) (some (8, 3, 6)) (some (8, 4, 6))
    (.next ([-45000000000], [2400000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next
    ([-150000000000], [7230000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-45000000000],
    [1215000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-480000000000], [6900000000000])
    (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-465000000000], [5580000000000]) (some (8, 4, 6))
    (some (8, 4, 6)) (.next ([-465000000000], [4755000000000]) (some (8, 4, 6)) (some (8, 4, 6))
    fan46Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan47Owner4Part0 : FanWitness := (.next ([5850000000000], [375000000000]) (some (4, 1, 5)) (some
    (4, 1, 5)) (.next ([5130000000000], [720000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([6930000000000, -9000000000000], [1260000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1,
    5)) (.next ([5505000000000, 0], [1260000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1,
    5)) (.next ([4305000000000], [1260000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([4590000000000, -9000000000000], [1635000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1,
    5)) (.next ([5505000000000], [2685000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([1965000000000], [1635000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2880000000000],
    [3885000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1260000000000], [2625000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([375000000000], [1965000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([0, 0], [1260000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1,
    5)) (.next ([0, -9000000000000], [2625000000000, 0]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-375000000000], [6225000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-720000000000],
    [5850000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1260000000000, -9000000000000],
    [8190000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1260000000000, -9000000000000],
    [6765000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1260000000000],
    [5565000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1635000000000, -9000000000000],
    [6225000000000, 0]) (some (0, 2, 5)) (some (0, 5, 5)) (.next ([-2685000000000], [8190000000000])
    (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-1635000000000], [3600000000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.next ([-3885000000000], [6765000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-2625000000000], [3885000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-1965000000000], [2340000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5,
    4)) (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

theorem excluded40_1 : ExcludedOn (model40.B 1 ++ [step40.q]) 9000000000000 (model40.caps 1)
    (model40.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7740000000000, 9000000000000], [990000000000,
      -9000000000000]) none none (.next ([6480000000000], [2250000000000]) none none (.next
      ([5220000000000, -9000000000000], [2250000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([1260000000000, 9000000000000], [1260000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([0, 0], [1260000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-990000000000, 9000000000000], [8730000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-2250000000000], [8730000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2250000000000,
      0], [7470000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-1260000000000, -9000000000000], [2520000000000, 18000000000000]) (some (3, 1, 0)) (some (3,
      1, 3)) (.terminal (some (3, 1, 3)) none none))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_2 : ExcludedOn (model40.B 2 ++ [step40.q]) 9000000000000 (model40.caps 2)
    (model40.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2250000000000], [270000000000]) (some (0, 3, 1))
      (some (0, 3, 1)) (.next ([7740000000000, -9000000000000], [1260000000000, 9000000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([5220000000000, -9000000000000], [2250000000000, 0])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([990000000000, -9000000000000], [1530000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [1260000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-270000000000], [2520000000000])
      (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-1260000000000, -9000000000000], [9000000000000,
      0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2250000000000, 0], [7470000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1530000000000, -9000000000000],
      [2520000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_3 : ExcludedOn (model40.B 3 ++ [step40.q]) 9000000000000 (model40.caps 3)
    (model40.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2520000000000], [18000000000]) (some (2, 0, 4))
      (some (3, 0, 4)) (.next ([6732000000000], [1260000000000, 9000000000000]) (some (3, 0, 4))
      (some (3, 1, 4)) (.next ([6357000000000], [1635000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([1260000000000], [375000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([2520000000000], [6750000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([1260000000000,
      -9000000000000], [8010000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([885000000000], [8010000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0],
      [1260000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 4, 4)) (.next ([-18000000000],
      [2538000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.next ([-1260000000000, -9000000000000],
      [7992000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1635000000000],
      [7992000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-375000000000], [1635000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-6750000000000], [9270000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-8010000000000, -9000000000000], [9270000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-8010000000000], [8895000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_4 : ExcludedOn (model40.B 4 ++ [step40.q]) 9000000000000 (model40.caps 4)
    (model40.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_5 : ExcludedOn (model40.B 5 ++ [step40.q]) 9000000000000 (model40.caps 5)
    (model40.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_6 : ExcludedOn (model40.B 6 ++ [step40.q]) 9000000000000 (model40.caps 6)
    (model40.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_7 : ExcludedOn (model40.B 7 ++ [step40.q]) 9000000000000 (model40.caps 7)
    (model40.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded40_1
    · exact excluded40_2
    · exact excluded40_3
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
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_1 : ExcludedOn (model41.B 1 ++ [step41.q]) 9000000000000 (model41.caps 1)
    (model41.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_2 : ExcludedOn (model41.B 2 ++ [step41.q]) 9000000000000 (model41.caps 2)
    (model41.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_3 : ExcludedOn (model41.B 3 ++ [step41.q]) 9000000000000 (model41.caps 3)
    (model41.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_4 : ExcludedOn (model41.B 4 ++ [step41.q]) 9000000000000 (model41.caps 4)
    (model41.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_5 : ExcludedOn (model41.B 5 ++ [step41.q]) 9000000000000 (model41.caps 5)
    (model41.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_6 : ExcludedOn (model41.B 6 ++ [step41.q]) 9000000000000 (model41.caps 6)
    (model41.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1890000000000], [375000000000]) (some (4, 5, 2))
      (some (4, 5, 3)) (.next ([1875000000000], [420000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([30000000000], [15000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([5085000000000], [3915000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([1260000000000,
      9000000000000], [1260000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([5085000000000], [5175000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([3825000000000, -9000000000000], [3915000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([2820000000000], [5805000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2790000000000],
      [5790000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([630000000000, -9000000000000],
      [1635000000000, 9000000000000]) (some (0, 5, 3)) (some (5, 5, 3)) (.next ([615000000000,
      -9000000000000], [1680000000000, 9000000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next ([0,
      0], [1260000000000, 9000000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next ([-375000000000],
      [2265000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next ([-420000000000], [2295000000000])
      (some (5, 5, 3)) (some (5, 5, 3)) (.next ([-15000000000], [45000000000]) (some (5, 5, 3))
      (some (5, 5, 3)) (.next ([-3915000000000], [9000000000000]) (some (5, 5, 3)) (some (5, 5, 3))
      (.next ([-1260000000000, -9000000000000], [2520000000000, 18000000000000]) (some (5, 2, 3))
      (some (5, 2, 3)) (.next ([-5175000000000, -9000000000000], [10260000000000, 9000000000000])
      (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-3915000000000, 0], [7740000000000,
      -9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-5805000000000], [8625000000000])
      (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-5790000000000], [8580000000000]) (some (5, 2, 3))
      (some (5, 2, 3)) (.next ([-1635000000000, -9000000000000], [2265000000000]) (some (5, 2, 3))
      (some (5, 2, 3)) (.next ([-1680000000000, -9000000000000], [2295000000000]) (some (5, 2, 3))
      (some (5, 2, 4)) (.terminal (some (5, 2, 4)) (some (5, 2, 4)) (some (5, 2,
      4))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
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
    · exact excluded41_4
    · exact excluded41_5
    · exact excluded41_6
    · exact excluded41_7
    · exact excluded41_8
    · exact (hj rfl).elim
theorem next41 : model41.insert step41 = model42 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded42_0 : ExcludedOn (model42.B 0 ++ [step42.q]) 9000000000000 (model42.caps 0)
    (model42.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_1 : ExcludedOn (model42.B 1 ++ [step42.q]) 9000000000000 (model42.caps 1)
    (model42.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_2 : ExcludedOn (model42.B 2 ++ [step42.q]) 9000000000000 (model42.caps 2)
    (model42.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_3 : ExcludedOn (model42.B 3 ++ [step42.q]) 9000000000000 (model42.caps 3)
    (model42.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_4 : ExcludedOn (model42.B 4 ++ [step42.q]) 9000000000000 (model42.caps 4)
    (model42.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_5 : ExcludedOn (model42.B 5 ++ [step42.q]) 9000000000000 (model42.caps 5)
    (model42.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3960000000000], [750000000000]) (some (0, 0, 4))
      (some (0, 1, 4)) (.next ([5445000000000, 0], [1260000000000, 9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([2700000000000, -9000000000000], [750000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([2700000000000, -9000000000000], [2010000000000, 9000000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([4695000000000], [4710000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([735000000000], [3960000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([0], [5445000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-750000000000],
      [4710000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1260000000000, -9000000000000],
      [6705000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-750000000000, 0],
      [3450000000000, -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2010000000000,
      -9000000000000], [4710000000000]) (some (0, 2, 3)) (some (0, 4, 3)) (.next ([-4710000000000],
      [9405000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3960000000000], [4695000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4, 0)) (some (0, 4, 0)) (some (0, 4,
      0))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([3195000000000], [1890000000000]) (some (3, 0,
      1)) (some (3, 1, 2)) (.next ([4710000000000], [5040000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([2820000000000], [5040000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([45000000000], [4665000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([0],
      [5085000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1890000000000], [5085000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-5040000000000], [9750000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-5040000000000], [7860000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-4665000000000], [4710000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some
      (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded42_5
    · exact (hj rfl).elim
    · exact excluded42_7
    · exact excluded42_8
    · exact excluded42_9
theorem next42 : model42.insert step42 = model43 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded43_0 : ExcludedOn (model43.B 0 ++ [step43.q]) 9000000000000 (model43.caps 0)
    (model43.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_1 : ExcludedOn (model43.B 1 ++ [step43.q]) 9000000000000 (model43.caps 1)
    (model43.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4710000000000], [3780000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([1260000000000, 9000000000000], [1260000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([4710000000000], [5040000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([3450000000000, -9000000000000], [6300000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [1260000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-3780000000000, 9000000000000],
      [8490000000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-1260000000000,
      -9000000000000], [2520000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-5040000000000], [9750000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-6300000000000,
      -9000000000000], [9750000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
      0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded43_2 : ExcludedOn (model43.B 2 ++ [step43.q]) 9000000000000 (model43.caps 2)
    (model43.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_3 : ExcludedOn (model43.B 3 ++ [step43.q]) 9000000000000 (model43.caps 3)
    (model43.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_4 : ExcludedOn (model43.B 4 ++ [step43.q]) 9000000000000 (model43.caps 4)
    (model43.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_5 : ExcludedOn (model43.B 5 ++ [step43.q]) 9000000000000 (model43.caps 5)
    (model43.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded43_2
    · exact excluded43_3
    · exact excluded43_4
    · exact excluded43_5
    · exact (hj rfl).elim
    · exact excluded43_7
    · exact excluded43_8
    · exact excluded43_9
theorem next43 : model43.insert step43 = model44 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded44_0 : ExcludedOn (model44.B 0 ++ [step44.q]) 9000000000000 (model44.caps 0)
    (model44.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_1 : ExcludedOn (model44.B 1 ++ [step44.q]) 9000000000000 (model44.caps 1)
    (model44.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_2 : ExcludedOn (model44.B 2 ++ [step44.q]) 9000000000000 (model44.caps 2)
    (model44.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_3 : ExcludedOn (model44.B 3 ++ [step44.q]) 9000000000000 (model44.caps 3)
    (model44.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_4 : ExcludedOn (model44.B 4 ++ [step44.q]) 9000000000000 (model44.caps 4)
    (model44.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2625000000000, -9000000000000], [0,
      9000000000000]) (some (5, 0, 3)) (some (5, 6, 3)) (.next ([5415000000000, 0], [885000000000,
      9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([5505000000000, 0], [1260000000000,
      9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([3075000000000, -9000000000000],
      [885000000000, 9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([5415000000000],
      [3120000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([5505000000000], [3495000000000])
      (some (5, 6, 3)) (some (5, 6, 3)) (.next ([2790000000000], [3510000000000]) (some (5, 6, 3))
      (some (5, 6, 3)) (.next ([2880000000000], [3885000000000]) (some (5, 6, 3)) (some (5, 6, 3))
      (.next ([450000000000], [885000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([1260000000000], [2625000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([1455000000000],
      [3960000000000]) (some (5, 6, 3)) (some (5, 6, 3)) fan44Owner4Part0)))))))))))) (den :=
      9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded44_6 : ExcludedOn (model44.B 6 ++ [step44.q]) 9000000000000 (model44.caps 6)
    (model44.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded44_1
    · exact excluded44_2
    · exact excluded44_3
    · exact excluded44_4
    · exact (hj rfl).elim
    · exact excluded44_6
    · exact excluded44_7
    · exact excluded44_8
    · exact excluded44_9
theorem next44 : model44.insert step44 = model45 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded45_0 : ExcludedOn (model45.B 0 ++ [step45.q]) 9000000000000 (model45.caps 0)
    (model45.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7170000000000], [60000000000]) (some (8, 2, 5))
      (some (8, 2, 5)) (.next ([7080000000000], [150000000000]) (some (8, 2, 5)) (some (8, 2, 5))
      (.next ([1170000000000], [45000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next
      ([6420000000000], [480000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([5115000000000],
      [465000000000]) (some (8, 2, 5)) (some (8, 2, 6)) (.next ([4290000000000], [465000000000])
      (some (8, 2, 6)) (some (8, 2, 6)) (.next ([5490000000000], [840000000000]) (some (8, 2, 6))
      (some (8, 2, 6)) (.next ([4665000000000], [840000000000]) (some (8, 2, 6)) (some (8, 2, 6))
      (.next ([5160000000000], [1590000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next
      ([1530000000000], [480000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([5070000000000],
      [1680000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([4335000000000], [1590000000000])
      (some (8, 2, 6)) (some (8, 2, 6)) (.next ([4245000000000], [1680000000000]) (some (8, 2, 6))
      (some (8, 2, 6)) (.next ([4410000000000], [2010000000000]) (some (8, 2, 6)) (some (8, 2, 6))
      (.next ([5370000000000], [2580000000000]) (some (8, 2, 6)) (some (8, 2, 6))
      fan45Owner0Part1)))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded45_1 : ExcludedOn (model45.B 1 ++ [step45.q]) 9000000000000 (model45.caps 1)
    (model45.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_2 : ExcludedOn (model45.B 2 ++ [step45.q]) 9000000000000 (model45.caps 2)
    (model45.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_4 : ExcludedOn (model45.B 4 ++ [step45.q]) 9000000000000 (model45.caps 4)
    (model45.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_5 : ExcludedOn (model45.B 5 ++ [step45.q]) 9000000000000 (model45.caps 5)
    (model45.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_6 : ExcludedOn (model45.B 6 ++ [step45.q]) 9000000000000 (model45.caps 6)
    (model45.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded45_0
    · exact excluded45_1
    · exact excluded45_2
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7170000000000], [60000000000]) (some (6, 8, 5))
      (some (6, 8, 5)) (.next ([2355000000000], [45000000000]) (some (6, 8, 5)) (some (6, 8, 5))
      (.next ([7080000000000], [150000000000]) (some (6, 8, 5)) (some (6, 8, 5)) (.next
      ([1170000000000], [45000000000]) (some (6, 8, 5)) (some (6, 8, 5)) (.next ([6420000000000],
      [480000000000]) (some (6, 8, 5)) (some (6, 8, 5)) (.next ([5115000000000], [465000000000])
      (some (6, 8, 5)) (some (6, 8, 6)) (.next ([4290000000000], [465000000000]) (some (6, 8, 6))
      (some (6, 8, 6)) (.next ([5490000000000], [840000000000]) (some (6, 8, 6)) (some (6, 8, 6))
      (.next ([4665000000000], [840000000000]) (some (6, 8, 6)) (some (6, 8, 6)) (.next
      ([5160000000000], [1590000000000]) (some (6, 8, 6)) (some (6, 8, 6)) (.next ([1530000000000],
      [480000000000]) (some (6, 8, 6)) (some (6, 8, 6)) (.next ([5070000000000], [1680000000000])
      (some (6, 8, 6)) (some (7, 8, 6)) (.next ([4335000000000], [1590000000000]) (some (7, 8, 6))
      (some (7, 8, 6)) (.next ([4245000000000], [1680000000000]) (some (7, 8, 6)) (some (7, 8, 6))
      (.next ([4410000000000], [2010000000000]) (some (7, 8, 6)) (some (7, 8, 6))
      fan46Owner0Part1)))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded46_1 : ExcludedOn (model46.B 1 ++ [step46.q]) 9000000000000 (model46.caps 1)
    (model46.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_2 : ExcludedOn (model46.B 2 ++ [step46.q]) 9000000000000 (model46.caps 2)
    (model46.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_3 : ExcludedOn (model46.B 3 ++ [step46.q]) 9000000000000 (model46.caps 3)
    (model46.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_5 : ExcludedOn (model46.B 5 ++ [step46.q]) 9000000000000 (model46.caps 5)
    (model46.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3960000000000], [750000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([5505000000000, 0], [1260000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([6225000000000], [3150000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([2700000000000, -9000000000000], [2010000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([4965000000000, -9000000000000], [4410000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 3)) (.next ([2265000000000], [2400000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([2355000000000], [3870000000000]) (some (4, 1, 3)) (some (4, 1, 4))
      (.next ([795000000000], [3960000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [5505000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-750000000000], [4710000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1260000000000, -9000000000000], [6765000000000,
      9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-3150000000000], [9375000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2010000000000, -9000000000000], [4710000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4410000000000, -9000000000000], [9375000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2400000000000], [4665000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-3870000000000], [6225000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-3960000000000], [4755000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded46_6 : ExcludedOn (model46.B 6 ++ [step46.q]) 9000000000000 (model46.caps 6)
    (model46.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded46_3
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_2 : ExcludedOn (model47.B 2 ++ [step47.q]) 9000000000000 (model47.caps 2)
    (model47.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_3 : ExcludedOn (model47.B 3 ++ [step47.q]) 9000000000000 (model47.caps 3)
    (model47.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7365000000000], [450000000000]) (some (3, 0, 5))
      (some (4, 0, 5)) (.next ([5625000000000], [630000000000, 9000000000000]) (some (4, 0, 5))
      (some (4, 5, 5)) (.next ([5250000000000], [1005000000000]) (some (4, 5, 5)) (some (4, 5, 5))
      (.next ([7542000000000], [1458000000000]) (some (4, 5, 5)) (some (4, 5, 5)) (.next
      ([6357000000000], [1635000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([1260000000000],
      [375000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([5805000000000], [2565000000000])
      (some (4, 5, 3)) (some (4, 5, 3)) (.next ([1107000000000], [630000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([630000000000], [4995000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([810000000000], [8190000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0],
      [1260000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([-450000000000],
      [7815000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-630000000000, -9000000000000],
      [6255000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1005000000000],
      [6255000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1458000000000], [9000000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1635000000000], [7992000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-375000000000], [1635000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-2565000000000], [8370000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-630000000000], [1737000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4995000000000],
      [5625000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-8190000000000], [9000000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5,
      3))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded47_4 : ExcludedOn (model47.B 4 ++ [step47.q]) 9000000000000 (model47.caps 4)
    (model47.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2625000000000, -9000000000000], [0,
      9000000000000]) (some (4, 0, 5)) (some (4, 1, 5)) fan47Owner4Part0)) (den := 9000000000000)
      (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded47_5 : ExcludedOn (model47.B 5 ++ [step47.q]) 9000000000000 (model47.caps 5)
    (model47.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4230000000000], [60000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([8190000000000], [810000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([3960000000000], [750000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([5505000000000, 0], [1260000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([6930000000000, -9000000000000], [2070000000000, 9000000000000]) (some (4, 1, 2)) (some (4,
      1, 2)) (.next ([4695000000000], [3495000000000]) (some (4, 1, 2)) (some (4, 1, 4)) (.next
      ([2700000000000, -9000000000000], [2010000000000, 9000000000000]) (some (0, 1, 4)) (some (0,
      1, 4)) (.next ([795000000000], [3960000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [5505000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-60000000000], [4290000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-810000000000], [9000000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-750000000000], [4710000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-1260000000000, -9000000000000], [6765000000000, 9000000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2070000000000, -9000000000000], [9000000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-3495000000000], [8190000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-2010000000000, -9000000000000], [4710000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-3960000000000], [4755000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded47_6 : ExcludedOn (model47.B 6 ++ [step47.q]) 9000000000000 (model47.caps 6)
    (model47.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

end Sint140000150000
end ConwaySoifer.Simplified.Certificates
