/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint330000340000
import Mathlib.Tactic.FinCases

/-!
# Sint 330000 340000 2

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
namespace Sint330000340000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner0Part0 : FanWitness := (.next ([-1485000000000], [2970000000000]) (some (9, 4, 7))
    (some (9, 5, 7)) (.next ([-5040000000000], [9990000000000]) (some (9, 5, 7)) (some (9, 5, 7))
    (.next ([-375000000000], [735000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next
    ([-96000000000], [165000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next ([-3861000000000],
    [6096000000000]) (some (9, 5, 7)) (some (9, 5, 8)) (.next ([-4236000000000], [6096000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-4596000000000], [6471000000000]) (some (9, 5, 8))
    (some (9, 5, 8)) (.next ([-1860000000000], [2610000000000]) (some (9, 5, 8)) (some (9, 5, 8))
    (.next ([-4305000000000], [6000000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-3990000000000], [5475000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-3615000000000],
    [4740000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-4971000000000], [6471000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5249400000000, -1980000000000], [6652800000000,
    3960000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5040000000000], [6375000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-1485000000000], [1860000000000]) (some (9, 5, 8))
    (some (9, 5, 8)) (.next ([-3433200000000, 3960000000000], [4086600000000, -1980000000000]) (some
    (9, 5, 8)) (some (9, 5, 8)) (.next ([-5624400000000, -1980000000000], [6652800000000,
    3960000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5693400000000, -1980000000000],
    [6556800000000, 3960000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5475000000000],
    [6225000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5721000000000], [6471000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-6096000000000], [6471000000000]) (some (9, 5, 8))
    (some (9, 5, 8)) (.next ([-2041800000000, -3960000000000], [2138400000000, 1980000000000]) (some
    (9, 5, 8)) (some (9, 5, 8)) (.next ([-6165000000000], [6375000000000]) (some (9, 5, 8)) (some
    (9, 5, 8)) (.next ([-6081000000000], [6096000000000]) (some (9, 5, 8)) (some (9, 5, 8))
    (.terminal (some (9, 5, 8)) (some (9, 5, 8)) (some (9, 5, 8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner0Part1 : FanWitness := (.next ([653400000000, 1980000000000], [3433200000000,
    -3960000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([1028400000000, 1980000000000],
    [5624400000000, 1980000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([863400000000,
    1980000000000], [5693400000000, 1980000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([750000000000], [5475000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([750000000000],
    [5721000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([375000000000], [6096000000000])
    (some (9, 4, 6)) (some (9, 4, 6)) (.next ([96600000000, -1980000000000], [2041800000000,
    3960000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([210000000000], [6165000000000]) (some
    (9, 4, 6)) (some (9, 4, 6)) (.next ([15000000000], [6081000000000]) (some (9, 4, 6)) (some (9,
    4, 6)) (.next ([0], [2220000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-360000000000],
    [6456000000000]) (some (9, 4, 6)) (some (9, 4, 7)) (.next ([-525000000000], [6525000000000])
    (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-735000000000], [5346000000000]) (some (9, 4, 7))
    (some (9, 4, 7)) (.next ([-96000000000], [540000000000]) (some (9, 4, 7)) (some (9, 4, 7))
    (.next ([-735000000000], [3990000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next
    ([-1110000000000], [5721000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-375000000000],
    [1860000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-1275000000000], [5790000000000])
    (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-181800000000, -3960000000000], [653400000000,
    1980000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-556800000000, -3960000000000],
    [1388400000000, 1980000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-4596000000000],
    [10086000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-360000000000], [735000000000])
    (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-4971000000000], [10086000000000]) (some (9, 4, 7))
    (some (9, 4, 7)) (.next ([-735000000000], [1485000000000]) (some (9, 4, 7)) (some (9, 4, 7))
    fan19Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner0Part2 : FanWitness := (.next ([4611000000000], [1110000000000]) (some (8, 9, 6))
    (some (8, 9, 6)) (.next ([1485000000000], [375000000000]) (some (8, 9, 6)) (some (8, 9, 6))
    (.next ([4515000000000], [1275000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
    ([471600000000, -1980000000000], [181800000000, 3960000000000]) (some (8, 9, 6)) (some (8, 9,
    6)) (.next ([831600000000, -1980000000000], [556800000000, 3960000000000]) (some (8, 9, 6))
    (some (8, 9, 6)) (.next ([5490000000000], [4596000000000]) (some (8, 9, 6)) (some (8, 9, 6))
    (.next ([375000000000], [360000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
    ([5115000000000], [4971000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([750000000000],
    [735000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([1485000000000], [1485000000000])
    (some (8, 9, 6)) (some (8, 9, 6)) (.next ([4950000000000], [5040000000000]) (some (8, 9, 6))
    (some (8, 9, 6)) (.next ([360000000000], [375000000000]) (some (8, 9, 6)) (some (9, 9, 6))
    (.next ([69000000000], [96000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next ([2235000000000],
    [3861000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next ([1860000000000], [4236000000000])
    (some (9, 9, 6)) (some (9, 9, 6)) (.next ([1875000000000], [4596000000000]) (some (9, 9, 6))
    (some (9, 9, 6)) (.next ([750000000000], [1860000000000]) (some (9, 9, 6)) (some (9, 9, 6))
    (.next ([1695000000000], [4305000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next
    ([1485000000000], [3990000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next ([1125000000000],
    [3615000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([1500000000000], [4971000000000])
    (some (9, 4, 6)) (some (9, 4, 6)) (.next ([1403400000000, 1980000000000], [5249400000000,
    1980000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([1335000000000], [5040000000000])
    (some (9, 4, 6)) (some (9, 4, 6)) (.next ([375000000000], [1485000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) fan19Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner0Part0 : FanWitness := (.next ([-1485000000000], [2970000000000]) (some (9, 4, 7))
    (some (9, 5, 7)) (.next ([-375000000000], [735000000000]) (some (9, 5, 7)) (some (9, 5, 7))
    (.next ([-1980000000000], [3480000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next
    ([-96000000000], [165000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next ([-3861000000000],
    [6096000000000]) (some (9, 5, 7)) (some (9, 5, 8)) (.next ([-6576000000000], [9951000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-4236000000000], [6096000000000]) (some (9, 5, 8))
    (some (9, 5, 8)) (.next ([-6951000000000], [9951000000000]) (some (9, 5, 8)) (some (9, 5, 8))
    (.next ([-2715000000000], [3855000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-4596000000000], [6471000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-7020000000000],
    [9855000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-1860000000000], [2610000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-4305000000000], [6000000000000]) (some (9, 5, 8))
    (some (9, 5, 8)) (.next ([-4971000000000], [6471000000000]) (some (9, 5, 8)) (some (9, 5, 8))
    (.next ([-5249400000000, -1980000000000], [6652800000000, 3960000000000]) (some (9, 5, 8)) (some
    (9, 5, 8)) (.next ([-5040000000000], [6375000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-1485000000000], [1860000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5624400000000,
    -1980000000000], [6652800000000, 3960000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-5693400000000, -1980000000000], [6556800000000, 3960000000000]) (some (9, 5, 8)) (some (9, 5,
    8)) (.next ([-5721000000000], [6471000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-6096000000000], [6471000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-2041800000000,
    -3960000000000], [2138400000000, 1980000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-6165000000000], [6375000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-6081000000000],
    [6096000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.terminal (some (9, 5, 8)) (some (9, 5, 8))
    (some (9, 5, 8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner0Part1 : FanWitness := (.next ([1335000000000], [5040000000000]) (some (9, 9, 6))
    (some (9, 9, 6)) (.next ([375000000000], [1485000000000]) (some (9, 9, 6)) (some (9, 9, 6))
    (.next ([1028400000000, 1980000000000], [5624400000000, 1980000000000]) (some (9, 9, 6)) (some
    (9, 9, 6)) (.next ([863400000000, 1980000000000], [5693400000000, 1980000000000]) (some (9, 9,
    6)) (some (9, 9, 6)) (.next ([750000000000], [5721000000000]) (some (9, 9, 6)) (some (9, 9, 6))
    (.next ([375000000000], [6096000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next ([96600000000,
    -1980000000000], [2041800000000, 3960000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next
    ([210000000000], [6165000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next ([15000000000],
    [6081000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next ([0], [2220000000000]) (some (9, 9,
    6)) (some (9, 9, 6)) (.next ([-360000000000], [6456000000000]) (some (9, 9, 6)) (some (9, 9, 7))
    (.next ([-525000000000], [6525000000000]) (some (9, 9, 7)) (some (9, 9, 7)) (.next
    ([-495000000000], [3855000000000]) (some (9, 9, 7)) (some (9, 9, 7)) (.next ([-735000000000],
    [5346000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-96000000000], [540000000000]) (some
    (9, 4, 7)) (some (9, 4, 7)) (.next ([-1110000000000], [5721000000000]) (some (9, 4, 7)) (some
    (9, 4, 7)) (.next ([-375000000000], [1860000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next
    ([-1275000000000], [5790000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-1230000000000],
    [5340000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-855000000000], [3480000000000])
    (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-181800000000, -3960000000000], [653400000000,
    1980000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-1326600000000, 1980000000000],
    [3298200000000, -3960000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-360000000000],
    [735000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-735000000000], [1485000000000])
    (some (9, 4, 7)) (some (9, 4, 7)) fan22Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner0Part2 : FanWitness := (.next ([4611000000000], [1110000000000]) (some (8, 9, 6))
    (some (8, 9, 6)) (.next ([1485000000000], [375000000000]) (some (8, 9, 6)) (some (8, 9, 6))
    (.next ([4515000000000], [1275000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
    ([4110000000000], [1230000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([2625000000000],
    [855000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([471600000000, -1980000000000],
    [181800000000, 3960000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([1971600000000,
    -1980000000000], [1326600000000, -1980000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
    ([375000000000], [360000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([750000000000],
    [735000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([1485000000000], [1485000000000])
    (some (8, 9, 6)) (some (8, 9, 6)) (.next ([360000000000], [375000000000]) (some (8, 9, 6)) (some
    (8, 9, 6)) (.next ([1500000000000], [1980000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
    ([69000000000], [96000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([2235000000000],
    [3861000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([3375000000000], [6576000000000])
    (some (8, 9, 6)) (some (8, 9, 6)) (.next ([1860000000000], [4236000000000]) (some (8, 9, 6))
    (some (8, 9, 6)) (.next ([3000000000000], [6951000000000]) (some (8, 9, 6)) (some (8, 9, 6))
    (.next ([1140000000000], [2715000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
    ([1875000000000], [4596000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([2835000000000],
    [7020000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([750000000000], [1860000000000])
    (some (8, 9, 6)) (some (9, 9, 6)) (.next ([1695000000000], [4305000000000]) (some (9, 9, 6))
    (some (9, 9, 6)) (.next ([1500000000000], [4971000000000]) (some (9, 9, 6)) (some (9, 9, 6))
    (.next ([1403400000000, 1980000000000], [5249400000000, 1980000000000]) (some (9, 9, 6)) (some
    (9, 9, 6)) fan22Owner0Part1))))))))))))))))))))))))

theorem excluded16_0 : ExcludedOn (model16.B 0 ++ [step16.q]) 9000000000000 (model16.caps 0)
    (model16.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_1 : ExcludedOn (model16.B 1 ++ [step16.q]) 9000000000000 (model16.caps 1)
    (model16.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_2 : ExcludedOn (model16.B 2 ++ [step16.q]) 9000000000000 (model16.caps 2)
    (model16.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_3 : ExcludedOn (model16.B 3 ++ [step16.q]) 9000000000000 (model16.caps 3)
    (model16.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_4 : ExcludedOn (model16.B 4 ++ [step16.q]) 9000000000000 (model16.caps 4)
    (model16.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3960000000000], [165000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([3654000000000], [471000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([2805000000000, 9000000000000], [1155000000000, -9000000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([2499000000000, 9000000000000], [1155000000000, -9000000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([5010000000000], [4125000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([4704000000000], [4125000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([2970000000000, 9000000000000], [2970000000000, 9000000000000]) (some (5, 1, 2)) (some
      (5, 1, 2)) (.next ([2205000000000, -9000000000000], [2970000000000, 9000000000000]) (some (5,
      1, 2)) (some (5, 1, 2)) (.next ([990000000000, -9000000000000], [3135000000000,
      9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([684000000000, -9000000000000],
      [3441000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([0, 0],
      [2970000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([-165000000000],
      [4125000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next ([-471000000000], [4125000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-1155000000000, 9000000000000], [3960000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-1155000000000, 9000000000000], [3654000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-4125000000000], [9135000000000]) (some (5, 1, 3))
      (some (5, 1, 4)) (.next ([-4125000000000], [8829000000000]) (some (5, 1, 4)) (some (5, 1, 4))
      (.next ([-2970000000000, -9000000000000], [5940000000000, 18000000000000]) (some (5, 1, 4))
      (some (5, 1, 4)) (.next ([-2970000000000, -9000000000000], [5175000000000]) (some (5, 1, 4))
      (some (5, 1, 4)) (.next ([-3135000000000, -9000000000000], [4125000000000, 0]) (some (5, 1,
      4)) (some (5, 1, 5)) (.next ([-3441000000000, -9000000000000], [4125000000000, 0]) (some (5,
      1, 5)) (some (5, 2, 5)) (.terminal (some (5, 2, 5)) (some (0, 2, 5)) (some (5, 2,
      5))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded16_5 : ExcludedOn (model16.B 5 ++ [step16.q]) 9000000000000 (model16.caps 5)
    (model16.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_6 : ExcludedOn (model16.B 6 ++ [step16.q]) 9000000000000 (model16.caps 6)
    (model16.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_7 : ExcludedOn (model16.B 7 ++ [step16.q]) 9000000000000 (model16.caps 7)
    (model16.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_9 : ExcludedOn (model16.B 9 ++ [step16.q]) 9000000000000 (model16.caps 9)
    (model16.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked16 : StepValid model16 9000000000000 step16 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded16_0
    · exact excluded16_1
    · exact excluded16_2
    · exact excluded16_3
    · exact excluded16_4
    · exact excluded16_5
    · exact excluded16_6
    · exact excluded16_7
    · exact (hj rfl).elim
    · exact excluded16_9
theorem next16 : model16.insert step16 = model17 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded17_0 : ExcludedOn (model17.B 0 ++ [step17.q]) 9000000000000 (model17.caps 0)
    (model17.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_1 : ExcludedOn (model17.B 1 ++ [step17.q]) 9000000000000 (model17.caps 1)
    (model17.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_2 : ExcludedOn (model17.B 2 ++ [step17.q]) 9000000000000 (model17.caps 2)
    (model17.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_3 : ExcludedOn (model17.B 3 ++ [step17.q]) 9000000000000 (model17.caps 3)
    (model17.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5625000000000], [405000000000]) (some (2, 4, 1))
      (some (3, 4, 2)) (.next ([2655000000000, -9000000000000], [405000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([4545000000000], [2175000000000, 9000000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([4545000000000], [2970000000000, 9000000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([4140000000000], [5235000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([4140000000000], [6030000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([795000000000], [3750000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0],
      [2970000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-405000000000],
      [6030000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-405000000000], [3060000000000,
      -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2175000000000, -9000000000000],
      [6720000000000, 9000000000000]) (some (0, 4, 2)) (some (4, 4, 2)) (.next ([-2970000000000,
      -9000000000000], [7515000000000, 9000000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next
      ([-5235000000000], [9375000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next
      ([-6030000000000], [10170000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-3750000000000], [4545000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.terminal (some (4, 1,
      2)) (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded17_5 : ExcludedOn (model17.B 5 ++ [step17.q]) 9000000000000 (model17.caps 5)
    (model17.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_6 : ExcludedOn (model17.B 6 ++ [step17.q]) 9000000000000 (model17.caps 6)
    (model17.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_7 : ExcludedOn (model17.B 7 ++ [step17.q]) 9000000000000 (model17.caps 7)
    (model17.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_8 : ExcludedOn (model17.B 8 ++ [step17.q]) 9000000000000 (model17.caps 8)
    (model17.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6030000000000], [3375000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([2205000000000], [3375000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([1170000000000], [4860000000000]) (some (0, 1, 3)) (some (0, 3, 3)) (.next
      ([720000000000], [3825000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0],
      [3825000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-3375000000000], [9405000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-3375000000000], [5580000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-4860000000000], [6030000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-3825000000000], [4545000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded17_9 : ExcludedOn (model17.B 9 ++ [step17.q]) 9000000000000 (model17.caps 9)
    (model17.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked17 : StepValid model17 9000000000000 step17 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded17_0
    · exact excluded17_1
    · exact excluded17_2
    · exact excluded17_3
    · exact (hj rfl).elim
    · exact excluded17_5
    · exact excluded17_6
    · exact excluded17_7
    · exact excluded17_8
    · exact excluded17_9
theorem next17 : model17.insert step17 = model18 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded18_0 : ExcludedOn (model18.B 0 ++ [step18.q]) 9000000000000 (model18.caps 0)
    (model18.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_1 : ExcludedOn (model18.B 1 ++ [step18.q]) 9000000000000 (model18.caps 1)
    (model18.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_2 : ExcludedOn (model18.B 2 ++ [step18.q]) 9000000000000 (model18.caps 2)
    (model18.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_3 : ExcludedOn (model18.B 3 ++ [step18.q]) 9000000000000 (model18.caps 3)
    (model18.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_5 : ExcludedOn (model18.B 5 ++ [step18.q]) 9000000000000 (model18.caps 5)
    (model18.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5625000000000], [615000000000]) (some (3, 0, 2))
      (some (3, 1, 2)) (.next ([5625000000000, 0], [2970000000000, 9000000000000]) (some (3, 1, 2))
      (some (4, 1, 2)) (.next ([3270000000000, -9000000000000], [2970000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2970000000000, 9000000000000], [2970000000000,
      9000000000000]) (some (4, 1, 2)) (some (4, 1, 3)) (.next ([2970000000000, 9000000000000],
      [3270000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0, 0],
      [2970000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-615000000000],
      [6240000000000]) (some (4, 1, 3)) (some (4, 2, 3)) (.next ([-2970000000000, -9000000000000],
      [8595000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-2970000000000,
      -9000000000000], [6240000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-2970000000000,
      -9000000000000], [5940000000000, 18000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-3270000000000, 9000000000000], [6240000000000, 0]) (some (4, 2, 3)) (some (4, 2, 3))
      (.terminal (some (4, 2, 3)) (some (0, 2, 3)) (some (4, 2, 3))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_6 : ExcludedOn (model18.B 6 ++ [step18.q]) 9000000000000 (model18.caps 6)
    (model18.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_7 : ExcludedOn (model18.B 7 ++ [step18.q]) 9000000000000 (model18.caps 7)
    (model18.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_8 : ExcludedOn (model18.B 8 ++ [step18.q]) 9000000000000 (model18.caps 8)
    (model18.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_9 : ExcludedOn (model18.B 9 ++ [step18.q]) 9000000000000 (model18.caps 9)
    (model18.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked18 : StepValid model18 9000000000000 step18 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded18_0
    · exact excluded18_1
    · exact excluded18_2
    · exact excluded18_3
    · exact (hj rfl).elim
    · exact excluded18_5
    · exact excluded18_6
    · exact excluded18_7
    · exact excluded18_8
    · exact excluded18_9
theorem next18 : model18.insert step18 = model19 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded19_0 : ExcludedOn (model19.B 0 ++ [step19.q]) 9000000000000 (model19.caps 0)
    (model19.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6096000000000], [360000000000]) (some (8, 9, 5))
      (some (8, 9, 5)) (.next ([6000000000000], [525000000000]) (some (8, 9, 5)) (some (8, 9, 5))
      (.next ([4611000000000], [735000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next
      ([444000000000], [96000000000]) (some (8, 9, 5)) (some (8, 9, 6)) (.next ([3255000000000],
      [735000000000]) (some (8, 9, 6)) (some (8, 9, 6)) fan19Owner0Part2)))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_1 : ExcludedOn (model19.B 1 ++ [step19.q]) 9000000000000 (model19.caps 1)
    (model19.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_2 : ExcludedOn (model19.B 2 ++ [step19.q]) 9000000000000 (model19.caps 2)
    (model19.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_3 : ExcludedOn (model19.B 3 ++ [step19.q]) 9000000000000 (model19.caps 3)
    (model19.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_5 : ExcludedOn (model19.B 5 ++ [step19.q]) 9000000000000 (model19.caps 5)
    (model19.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4260000000000, 0], [1770000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([2760000000000], [1980000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3270000000000, -9000000000000], [2970000000000,
      9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2970000000000, 9000000000000],
      [2970000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 3)) (.next ([2970000000000,
      9000000000000], [3270000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([4260000000000], [4740000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1290000000000,
      -9000000000000], [7710000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0,
      0], [2970000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-1770000000000,
      9000000000000], [6030000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 2, 3)) (.next
      ([-1980000000000], [4740000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2970000000000,
      -9000000000000], [6240000000000]) (some (0, 2, 3)) (some (0, 2, 4)) (.next ([-2970000000000,
      -9000000000000], [5940000000000, 18000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-3270000000000, 9000000000000], [6240000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-4740000000000], [9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-7710000000000,
      -9000000000000], [9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_6 : ExcludedOn (model19.B 6 ++ [step19.q]) 9000000000000 (model19.caps 6)
    (model19.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_7 : ExcludedOn (model19.B 7 ++ [step19.q]) 9000000000000 (model19.caps 7)
    (model19.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_8 : ExcludedOn (model19.B 8 ++ [step19.q]) 9000000000000 (model19.caps 8)
    (model19.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_9 : ExcludedOn (model19.B 9 ++ [step19.q]) 9000000000000 (model19.caps 9)
    (model19.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked19 : StepValid model19 9000000000000 step19 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded19_0
    · exact excluded19_1
    · exact excluded19_2
    · exact excluded19_3
    · exact (hj rfl).elim
    · exact excluded19_5
    · exact excluded19_6
    · exact excluded19_7
    · exact excluded19_8
    · exact excluded19_9
theorem next19 : model19.insert step19 = model20 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded20_0 : ExcludedOn (model20.B 0 ++ [step20.q]) 9000000000000 (model20.caps 0)
    (model20.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_2 : ExcludedOn (model20.B 2 ++ [step20.q]) 9000000000000 (model20.caps 2)
    (model20.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_3 : ExcludedOn (model20.B 3 ++ [step20.q]) 9000000000000 (model20.caps 3)
    (model20.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_5 : ExcludedOn (model20.B 5 ++ [step20.q]) 9000000000000 (model20.caps 5)
    (model20.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3960000000000], [405000000000]) (some (3, 0, 2))
      (some (3, 1, 2)) (.next ([5835000000000, 0], [1095000000000, 9000000000000]) (some (3, 1, 2))
      (some (4, 1, 2)) (.next ([1875000000000, 0], [990000000000, -9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([3270000000000, -9000000000000], [2970000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2970000000000, 9000000000000], [2970000000000,
      9000000000000]) (some (4, 1, 2)) (some (4, 1, 3)) (.next ([2970000000000, 9000000000000],
      [3270000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1875000000000],
      [3960000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0, 0], [2970000000000,
      9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-405000000000], [4365000000000])
      (some (4, 1, 3)) (some (4, 2, 3)) (.next ([-1095000000000, -9000000000000], [6930000000000,
      9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-990000000000, 9000000000000],
      [2865000000000, -9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-2970000000000,
      -9000000000000], [6240000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2970000000000,
      -9000000000000], [5940000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-3270000000000, 9000000000000], [6240000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-3960000000000], [5835000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_6 : ExcludedOn (model20.B 6 ++ [step20.q]) 9000000000000 (model20.caps 6)
    (model20.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_7 : ExcludedOn (model20.B 7 ++ [step20.q]) 9000000000000 (model20.caps 7)
    (model20.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_8 : ExcludedOn (model20.B 8 ++ [step20.q]) 9000000000000 (model20.caps 8)
    (model20.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_9 : ExcludedOn (model20.B 9 ++ [step20.q]) 9000000000000 (model20.caps 9)
    (model20.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked20 : StepValid model20 9000000000000 step20 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded20_0
    · exact excluded20_1
    · exact excluded20_2
    · exact excluded20_3
    · exact (hj rfl).elim
    · exact excluded20_5
    · exact excluded20_6
    · exact excluded20_7
    · exact excluded20_8
    · exact excluded20_9
theorem next20 : model20.insert step20 = model21 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded21_0 : ExcludedOn (model21.B 0 ++ [step21.q]) 9000000000000 (model21.caps 0)
    (model21.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_1 : ExcludedOn (model21.B 1 ++ [step21.q]) 9000000000000 (model21.caps 1)
    (model21.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_2 : ExcludedOn (model21.B 2 ++ [step21.q]) 9000000000000 (model21.caps 2)
    (model21.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_3 : ExcludedOn (model21.B 3 ++ [step21.q]) 9000000000000 (model21.caps 3)
    (model21.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_5 : ExcludedOn (model21.B 5 ++ [step21.q]) 9000000000000 (model21.caps 5)
    (model21.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3960000000000], [2790000000000]) (some (4, 0,
      2)) (some (4, 1, 2)) (.next ([3270000000000, -9000000000000], [2970000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2970000000000, 9000000000000], [2970000000000,
      9000000000000]) (some (4, 1, 2)) (some (4, 1, 3)) (.next ([2970000000000, 9000000000000],
      [3270000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([510000000000],
      [2280000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([990000000000, -9000000000000],
      [5760000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([180000000000,
      9000000000000], [3780000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0,
      0], [2970000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-2790000000000], [6750000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-2970000000000,
      -9000000000000], [6240000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2970000000000,
      -9000000000000], [5940000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-3270000000000, 9000000000000], [6240000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-2280000000000], [2790000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-5760000000000,
      -9000000000000], [6750000000000]) (some (0, 2, 3)) (some (0, 2, 4)) (.next ([-3780000000000,
      9000000000000], [3960000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded21_6 : ExcludedOn (model21.B 6 ++ [step21.q]) 9000000000000 (model21.caps 6)
    (model21.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_7 : ExcludedOn (model21.B 7 ++ [step21.q]) 9000000000000 (model21.caps 7)
    (model21.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_8 : ExcludedOn (model21.B 8 ++ [step21.q]) 9000000000000 (model21.caps 8)
    (model21.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_9 : ExcludedOn (model21.B 9 ++ [step21.q]) 9000000000000 (model21.caps 9)
    (model21.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked21 : StepValid model21 9000000000000 step21 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded21_0
    · exact excluded21_1
    · exact excluded21_2
    · exact excluded21_3
    · exact (hj rfl).elim
    · exact excluded21_5
    · exact excluded21_6
    · exact excluded21_7
    · exact excluded21_8
    · exact excluded21_9
theorem next21 : model21.insert step21 = model22 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded22_0 : ExcludedOn (model22.B 0 ++ [step22.q]) 9000000000000 (model22.caps 0)
    (model22.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6096000000000], [360000000000]) (some (8, 9, 5))
      (some (8, 9, 5)) (.next ([6000000000000], [525000000000]) (some (8, 9, 5)) (some (8, 9, 5))
      (.next ([3360000000000], [495000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next
      ([4611000000000], [735000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([444000000000],
      [96000000000]) (some (8, 9, 5)) (some (8, 9, 6)) fan22Owner0Part2)))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_1 : ExcludedOn (model22.B 1 ++ [step22.q]) 9000000000000 (model22.caps 1)
    (model22.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_2 : ExcludedOn (model22.B 2 ++ [step22.q]) 9000000000000 (model22.caps 2)
    (model22.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_3 : ExcludedOn (model22.B 3 ++ [step22.q]) 9000000000000 (model22.caps 3)
    (model22.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_5 : ExcludedOn (model22.B 5 ++ [step22.q]) 9000000000000 (model22.caps 5)
    (model22.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4395000000000], [2625000000000]) (some (4, 0,
      2)) (some (4, 1, 2)) (.next ([3270000000000, -9000000000000], [2970000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2970000000000, 9000000000000], [2970000000000,
      9000000000000]) (some (4, 1, 2)) (some (4, 1, 3)) (.next ([2970000000000, 9000000000000],
      [3270000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([780000000000],
      [1845000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1425000000000, -9000000000000],
      [5595000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([345000000000,
      9000000000000], [4050000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0,
      0], [2970000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-2625000000000], [7020000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-2970000000000,
      -9000000000000], [6240000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2970000000000,
      -9000000000000], [5940000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-3270000000000, 9000000000000], [6240000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-1845000000000], [2625000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-5595000000000,
      -9000000000000], [7020000000000]) (some (0, 2, 3)) (some (0, 2, 4)) (.next ([-4050000000000,
      9000000000000], [4395000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_6 : ExcludedOn (model22.B 6 ++ [step22.q]) 9000000000000 (model22.caps 6)
    (model22.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_7 : ExcludedOn (model22.B 7 ++ [step22.q]) 9000000000000 (model22.caps 7)
    (model22.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_8 : ExcludedOn (model22.B 8 ++ [step22.q]) 9000000000000 (model22.caps 8)
    (model22.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_9 : ExcludedOn (model22.B 9 ++ [step22.q]) 9000000000000 (model22.caps 9)
    (model22.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked22 : StepValid model22 9000000000000 step22 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded22_0
    · exact excluded22_1
    · exact excluded22_2
    · exact excluded22_3
    · exact (hj rfl).elim
    · exact excluded22_5
    · exact excluded22_6
    · exact excluded22_7
    · exact excluded22_8
    · exact excluded22_9
theorem next22 : model22.insert step22 = model23 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded23_0 : ExcludedOn (model23.B 0 ++ [step23.q]) 9000000000000 (model23.caps 0)
    (model23.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 7 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_1 : ExcludedOn (model23.B 1 ++ [step23.q]) 9000000000000 (model23.caps 1)
    (model23.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_2 : ExcludedOn (model23.B 2 ++ [step23.q]) 9000000000000 (model23.caps 2)
    (model23.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_3 : ExcludedOn (model23.B 3 ++ [step23.q]) 9000000000000 (model23.caps 3)
    (model23.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_4 : ExcludedOn (model23.B 4 ++ [step23.q]) 9000000000000 (model23.caps 4)
    (model23.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_5 : ExcludedOn (model23.B 5 ++ [step23.q]) 9000000000000 (model23.caps 5)
    (model23.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3780000000000, -9000000000000], [180000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([5760000000000, 9000000000000],
      [990000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 4)) (.next ([2280000000000],
      [510000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([3270000000000, -9000000000000],
      [2970000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([2970000000000,
      9000000000000], [2970000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([2970000000000, 9000000000000], [3270000000000, -9000000000000]) (some (3, 1, 4)) (some (3,
      1, 4)) (.next ([2790000000000], [3960000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0,
      0], [2970000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-180000000000,
      -9000000000000], [3960000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-990000000000,
      9000000000000], [6750000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-510000000000],
      [2790000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2970000000000, -9000000000000],
      [6240000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2970000000000, -9000000000000],
      [5940000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3270000000000,
      9000000000000], [6240000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-3960000000000], [6750000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded23_7 : ExcludedOn (model23.B 7 ++ [step23.q]) 9000000000000 (model23.caps 7)
    (model23.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_8 : ExcludedOn (model23.B 8 ++ [step23.q]) 9000000000000 (model23.caps 8)
    (model23.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_9 : ExcludedOn (model23.B 9 ++ [step23.q]) 9000000000000 (model23.caps 9)
    (model23.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked23 : StepValid model23 9000000000000 step23 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded23_0
    · exact excluded23_1
    · exact excluded23_2
    · exact excluded23_3
    · exact excluded23_4
    · exact excluded23_5
    · exact (hj rfl).elim
    · exact excluded23_7
    · exact excluded23_8
    · exact excluded23_9
theorem next23 : model23.insert step23 = model24 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint330000340000
end ConwaySoifer.Simplified.Certificates
