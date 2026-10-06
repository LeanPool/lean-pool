/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint190000200000
import Mathlib.Tactic.FinCases

/-!
# Sint 190000 200000 4

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
namespace Sint190000200000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner3Part0 : FanWitness := (.next ([5580000000000], [960000000000, 9000000000000]) (some
    (4, 1, 5)) (some (4, 5, 5)) (.next ([6960000000000], [1665000000000]) (some (4, 5, 5)) (some (4,
    5, 5)) (.next ([6105000000000], [1710000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5,
    3)) (.next ([5040000000000], [1500000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([1710000000000], [540000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([5685000000000],
    [2190000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([5565000000000], [2250000000000])
    (some (4, 5, 3)) (some (4, 5, 3)) (.next ([525000000000], [750000000000]) (some (4, 5, 3)) (some
    (4, 5, 3)) (.next ([750000000000], [4830000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([855000000000], [7770000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0], [1710000000000,
    9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0, -9000000000000], [540000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-855000000000, -9000000000000], [7770000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-855000000000], [7230000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-960000000000, -9000000000000], [6540000000000, 9000000000000]) (some
    (0, 5, 3)) (some (0, 5, 3)) (.next ([-1665000000000], [8625000000000]) (some (0, 5, 3)) (some
    (0, 5, 3)) (.next ([-1710000000000, -9000000000000], [7815000000000, 9000000000000]) (some (0,
    5, 3)) (some (0, 5, 3)) (.next ([-1500000000000], [6540000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([-540000000000], [2250000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-2190000000000], [7875000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2250000000000],
    [7815000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-750000000000], [1275000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4830000000000], [5580000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-7770000000000], [8625000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner3Part1 : FanWitness := (.next ([6915000000000, -9000000000000], [855000000000,
    9000000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([540000000000, -9000000000000], [0,
    9000000000000]) (some (4, 0, 5)) (some (4, 5, 5)) (.next ([6960000000000], [1665000000000])
    (some (4, 5, 5)) (some (4, 5, 5)) (.next ([6105000000000], [1710000000000, 9000000000000]) (some
    (4, 5, 3)) (some (4, 5, 3)) (.next ([5040000000000], [1500000000000]) (some (4, 5, 3)) (some (4,
    5, 3)) (.next ([1710000000000], [540000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([5685000000000], [2190000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([5565000000000],
    [2250000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([525000000000], [750000000000]) (some
    (4, 5, 3)) (some (4, 5, 3)) (.next ([750000000000], [4830000000000]) (some (4, 5, 3)) (some (4,
    5, 3)) (.next ([855000000000], [7770000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0],
    [1710000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([-855000000000],
    [7230000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-855000000000, -9000000000000],
    [7770000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0, -9000000000000], [540000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1665000000000], [8625000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-1710000000000, -9000000000000], [7815000000000, 9000000000000]) (some
    (0, 5, 3)) (some (0, 5, 3)) (.next ([-1500000000000], [6540000000000]) (some (0, 5, 3)) (some
    (0, 5, 3)) (.next ([-540000000000], [2250000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-2190000000000], [7875000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2250000000000],
    [7815000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-750000000000], [1275000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4830000000000], [5580000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-7770000000000], [8625000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner4Part0 : FanWitness := (.next ([390000000000], [2085000000000]) (some (6, 1, 7)) (some
    (6, 1, 7)) (.next ([30000000000], [600000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
    ([30000000000], [975000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([0, 0],
    [1710000000000, 9000000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([0, -9000000000000],
    [2625000000000, 0]) (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-177000000000], [4125000000000])
    (some (0, 1, 7)) (some (0, 2, 7)) (.next ([-375000000000], [8145000000000]) (some (0, 2, 7))
    (some (0, 2, 7)) (.next ([-177000000000], [3750000000000]) (some (0, 2, 7)) (some (0, 2, 7))
    (.next ([-375000000000], [5100000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
    ([-210000000000], [2715000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-585000000000],
    [3090000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-1005000000000], [5130000000000])
    (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-2085000000000, -9000000000000], [8145000000000, 0])
    (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-1380000000000], [5130000000000]) (some (0, 2, 7))
    (some (0, 2, 7)) (.next ([-2085000000000], [5520000000000]) (some (0, 2, 7)) (some (0, 2, 7))
    (.next ([-3192000000000], [7770000000000]) (some (0, 2, 7)) (some (0, 7, 7)) (.next
    ([-2715000000000, -9000000000000], [5130000000000, 0]) (some (0, 7, 6)) (some (0, 7, 6)) (.next
    ([-2625000000000], [4335000000000]) (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-4335000000000],
    [6663000000000]) (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-3015000000000], [4020000000000])
    (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-3015000000000], [3645000000000]) (some (0, 7, 6))
    (some (0, 7, 6)) (.next ([-2085000000000], [2475000000000]) (some (0, 7, 6)) (some (0, 7, 6))
    (.next ([-600000000000], [630000000000]) (some (0, 7, 6)) (some (0, 7, 6)) (.next
    ([-975000000000], [1005000000000]) (some (0, 7, 6)) (some (0, 7, 6)) (.terminal (some (0, 7, 6))
    (some (0, 7, 6)) (some (0, 7, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner5Part0 : FanWitness := (.next ([4500000000000], [570000000000]) (some (5, 1, 2)) (some
    (5, 1, 2)) (.next ([8145000000000], [1230000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([3645000000000], [660000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([4125000000000],
    [1005000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([5130000000000, 0], [1710000000000,
    9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([6435000000000, -9000000000000],
    [2940000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2790000000000,
    -9000000000000], [2280000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 5)) (.next
    ([3900000000000], [4245000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([2415000000000,
    -9000000000000], [2715000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([60000000000], [375000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([60000000000],
    [4500000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0], [5130000000000]) (some (0, 1,
    5)) (some (0, 1, 5)) (.next ([-225000000000], [4245000000000]) (some (0, 1, 5)) (some (0, 2, 5))
    (.next ([-570000000000], [5070000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1230000000000], [9375000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-660000000000],
    [4305000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1005000000000], [5130000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1710000000000, -9000000000000], [6840000000000,
    9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2940000000000, -9000000000000],
    [9375000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2280000000000, -9000000000000],
    [5070000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4245000000000], [8145000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2715000000000, -9000000000000], [5130000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-375000000000], [435000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-4500000000000], [4560000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner4Part0 : FanWitness := (.next ([30000000000], [975000000000]) (some (6, 1, 7)) (some
    (6, 1, 7)) (.next ([0, 0], [1710000000000, 9000000000000]) (some (6, 1, 7)) (some (6, 1, 7))
    (.next ([0, -9000000000000], [2625000000000, 0]) (some (0, 1, 7)) (some (0, 1, 7)) (.next
    ([-177000000000], [4125000000000]) (some (0, 1, 7)) (some (0, 2, 7)) (.next ([-177000000000],
    [3750000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-375000000000], [5100000000000])
    (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-210000000000], [2715000000000]) (some (0, 2, 7))
    (some (0, 2, 7)) (.next ([-1440000000000, -9000000000000], [7875000000000, 0]) (some (0, 2, 7))
    (some (0, 2, 7)) (.next ([-1005000000000], [5130000000000]) (some (0, 2, 7)) (some (0, 2, 7))
    (.next ([-1710000000000, -9000000000000], [6663000000000, 9000000000000]) (some (0, 2, 7)) (some
    (0, 2, 7)) (.next ([-1380000000000], [5130000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
    ([-1440000000000], [5250000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-2922000000000],
    [8145000000000]) (some (0, 2, 7)) (some (0, 7, 7)) (.next ([-2085000000000, -9000000000000],
    [5100000000000, 0]) (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-2715000000000, -9000000000000],
    [5130000000000, 0]) (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-2625000000000], [4335000000000])
    (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-2745000000000], [4395000000000]) (some (0, 7, 6))
    (some (0, 7, 6)) (.next ([-4335000000000], [6663000000000]) (some (0, 7, 6)) (some (0, 7, 6))
    (.next ([-2745000000000], [4020000000000]) (some (0, 7, 6)) (some (0, 7, 6)) (.next
    ([-2775000000000], [3420000000000]) (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-2085000000000],
    [2475000000000]) (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-600000000000], [630000000000])
    (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-7875000000000], [8145000000000]) (some (0, 7, 6))
    (some (0, 7, 6)) (.next ([-975000000000], [1005000000000]) (some (0, 7, 6)) (some (0, 7, 6))
    (.terminal (some (0, 7, 6)) (some (0, 7, 6)) (some (0, 7, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner6Part0 : FanWitness := (.next ([1140000000000, 9000000000000], [3360000000000,
    -9000000000000]) (some (4, 0, 6)) (some (4, 0, 6)) (.next ([630000000000], [4440000000000])
    (some (4, 0, 6)) (some (4, 0, 6)) (.next ([375000000000, 0], [3045000000000, -9000000000000])
    (some (4, 0, 6)) (some (4, 0, 6)) (.next ([330000000000, 9000000000000], [3420000000000,
    -9000000000000]) (some (4, 0, 6)) (some (4, 1, 6)) (.next ([60000000000], [750000000000]) (some
    (4, 1, 6)) (some (4, 1, 6)) (.next ([375000000000], [4755000000000]) (some (4, 1, 6)) (some (5,
    1, 6)) (.next ([60000000000], [4125000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0],
    [3375000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([-120000000000], [5250000000000])
    (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-570000000000], [5070000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-1335000000000, -9000000000000], [6465000000000, 9000000000000]) (some
    (0, 2, 6)) (some (0, 2, 6)) (.next ([-1380000000000], [5130000000000]) (some (0, 2, 6)) (some
    (0, 2, 6)) (.next ([-3495000000000], [8625000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-2280000000000, -9000000000000], [5070000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-1710000000000, -9000000000000], [3420000000000, 18000000000000]) (some (0, 2, 6)) (some (0,
    2, 6)) (.next ([-3090000000000, -9000000000000], [5130000000000]) (some (0, 2, 6)) (some (0, 2,
    6)) (.next ([-3870000000000, 0], [5580000000000, 9000000000000]) (some (0, 2, 6)) (some (0, 2,
    6)) (.next ([-3360000000000, 9000000000000], [4500000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-4440000000000], [5070000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-3045000000000, 9000000000000], [3420000000000, -9000000000000]) (some (0, 2, 4)) (some (0, 2,
    4)) (.next ([-3420000000000, 9000000000000], [3750000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([-750000000000], [810000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-4755000000000], [5130000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4125000000000],
    [4185000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2, 4)) (some (0, 2, 4))
    (some (0, 2, 4)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_1 : ExcludedOn (model32.B 1 ++ [step32.q]) 9000000000000 (model32.caps 1)
    (model32.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5070000000000], [2790000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([5070000000000], [4500000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([1710000000000, 9000000000000], [1710000000000, 9000000000000]) (some
      (0, 3, 2)) (some (0, 3, 2)) (.next ([3360000000000, -9000000000000], [6210000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [1710000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-2790000000000, 9000000000000],
      [7860000000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-4500000000000],
      [9570000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1710000000000, -9000000000000],
      [3420000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-6210000000000,
      -9000000000000], [9570000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
      0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded32_2 : ExcludedOn (model32.B 2 ++ [step32.q]) 9000000000000 (model32.caps 2)
    (model32.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_3 : ExcludedOn (model32.B 3 ++ [step32.q]) 9000000000000 (model32.caps 3)
    (model32.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_4 : ExcludedOn (model32.B 4 ++ [step32.q]) 9000000000000 (model32.caps 4)
    (model32.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_5 : ExcludedOn (model32.B 5 ++ [step32.q]) 9000000000000 (model32.caps 5)
    (model32.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4500000000000], [570000000000]) (some (0, 0, 5))
      (some (0, 1, 5)) (.next ([4125000000000], [1005000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([5130000000000, 0], [1710000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([2790000000000, -9000000000000], [2280000000000, 9000000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([3930000000000], [4500000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([2220000000000, -9000000000000], [4500000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([60000000000], [375000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([630000000000], [4305000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([570000000000],
      [3930000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([630000000000], [8430000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([60000000000], [4500000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([0], [5130000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-570000000000], [5070000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-1005000000000],
      [5130000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1710000000000, -9000000000000],
      [6840000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2280000000000,
      -9000000000000], [5070000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4500000000000],
      [8430000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4500000000000, 0],
      [6720000000000, -9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-375000000000],
      [435000000000]) (some (0, 2, 5)) (some (0, 5, 5)) (.next ([-4305000000000], [4935000000000])
      (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-3930000000000], [4500000000000]) (some (0, 5, 4))
      (some (0, 5, 4)) (.next ([-8430000000000], [9060000000000]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([-4500000000000], [4560000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some
      (0, 5, 4)) (some (0, 5, 0)) (some (0, 5, 4))))))))))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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

theorem excluded33_1 : ExcludedOn (model33.B 1 ++ [step33.q]) 9000000000000 (model33.caps 1)
    (model33.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_2 : ExcludedOn (model33.B 2 ++ [step33.q]) 9000000000000 (model33.caps 2)
    (model33.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_3 : ExcludedOn (model33.B 3 ++ [step33.q]) 9000000000000 (model33.caps 3)
    (model33.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (171) (241) (24100) (.witnessedFan (.next ([540000000000,
      -9000000000000], [0, 9000000000000]) (some (3, 0, 5)) (some (4, 0, 5)) (.next ([6915000000000,
      -9000000000000], [855000000000, 9000000000000]) (some (4, 0, 5)) (some (4, 1, 5)) (.next
      ([6375000000000], [855000000000]) (some (4, 1, 5)) (some (4, 1, 5)) fan33Owner3Part0))))
      (.witnessedFan (.next ([6375000000000], [855000000000]) (some (3, 0, 5)) (some (4, 0, 5))
      fan33Owner3Part1))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_4 : ExcludedOn (model33.B 4 ++ [step33.q]) 9000000000000 (model33.caps 4)
    (model33.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2625000000000, -9000000000000], [0,
      9000000000000]) (some (6, 0, 7)) (some (6, 1, 7)) (.next ([3948000000000], [177000000000])
      (some (6, 1, 7)) (some (6, 1, 7)) (.next ([7770000000000], [375000000000]) (some (6, 1, 7))
      (some (6, 1, 7)) (.next ([3573000000000], [177000000000]) (some (6, 1, 7)) (some (6, 1, 7))
      (.next ([4725000000000], [375000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
      ([2505000000000], [210000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([2505000000000],
      [585000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([4125000000000], [1005000000000])
      (some (6, 1, 7)) (some (6, 1, 7)) (.next ([6060000000000, -9000000000000], [2085000000000,
      9000000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([3750000000000], [1380000000000])
      (some (6, 1, 7)) (some (6, 1, 7)) (.next ([3435000000000], [2085000000000]) (some (6, 1, 7))
      (some (6, 1, 7)) (.next ([4578000000000], [3192000000000]) (some (6, 1, 7)) (some (6, 1, 7))
      (.next ([2415000000000, -9000000000000], [2715000000000, 9000000000000]) (some (6, 1, 7))
      (some (6, 1, 7)) (.next ([1710000000000], [2625000000000]) (some (6, 1, 7)) (some (6, 1, 7))
      (.next ([2328000000000], [4335000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
      ([1005000000000], [3015000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([630000000000],
      [3015000000000]) (some (6, 1, 7)) (some (6, 1, 7)) fan33Owner4Part0)))))))))))))))))) (den :=
      9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_5 : ExcludedOn (model33.B 5 ++ [step33.q]) 9000000000000 (model33.caps 5)
    (model33.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4020000000000], [225000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) fan33Owner5Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded33_1
    · exact excluded33_2
    · exact excluded33_3
    · exact excluded33_4
    · exact excluded33_5
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7020000000000], [585000000000]) (some (3, 0, 5))
      (some (4, 0, 5)) (.next ([5580000000000], [960000000000, 9000000000000]) (some (4, 0, 5))
      (some (4, 5, 5)) (.next ([7230000000000], [2040000000000]) (some (4, 5, 5)) (some (4, 5, 5))
      (.next ([5040000000000], [1500000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([1710000000000], [540000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([5565000000000],
      [2250000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([5955000000000], [2565000000000])
      (some (4, 5, 3)) (some (4, 5, 3)) (.next ([525000000000], [750000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([750000000000], [4830000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([1125000000000], [8145000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0],
      [1710000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([-585000000000],
      [7605000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-960000000000, -9000000000000],
      [6540000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2040000000000],
      [9270000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1500000000000], [6540000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-540000000000], [2250000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-2250000000000], [7815000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-2565000000000], [8520000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-750000000000], [1275000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4830000000000],
      [5580000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-8145000000000], [9270000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5,
      3))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded34_4 : ExcludedOn (model34.B 4 ++ [step34.q]) 9000000000000 (model34.caps 4)
    (model34.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2625000000000, -9000000000000], [0,
      9000000000000]) (some (6, 0, 7)) (some (6, 1, 7)) (.next ([3948000000000], [177000000000])
      (some (6, 1, 7)) (some (6, 1, 7)) (.next ([3573000000000], [177000000000]) (some (6, 1, 7))
      (some (6, 1, 7)) (.next ([4725000000000], [375000000000]) (some (6, 1, 7)) (some (6, 1, 7))
      (.next ([2505000000000], [210000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
      ([6435000000000, -9000000000000], [1440000000000, 9000000000000]) (some (6, 1, 7)) (some (6,
      1, 7)) (.next ([4125000000000], [1005000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
      ([4953000000000, 0], [1710000000000, 9000000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
      ([3750000000000], [1380000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([3810000000000],
      [1440000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([5223000000000], [2922000000000])
      (some (6, 1, 7)) (some (6, 1, 7)) (.next ([3015000000000, -9000000000000], [2085000000000,
      9000000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([2415000000000, -9000000000000],
      [2715000000000, 9000000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([1710000000000],
      [2625000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([1650000000000], [2745000000000])
      (some (6, 1, 7)) (some (6, 1, 7)) (.next ([2328000000000], [4335000000000]) (some (6, 1, 7))
      (some (6, 1, 7)) (.next ([1275000000000], [2745000000000]) (some (6, 1, 7)) (some (6, 1, 7))
      (.next ([645000000000], [2775000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
      ([390000000000], [2085000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([30000000000],
      [600000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([270000000000], [7875000000000])
      (some (6, 1, 7)) (some (6, 1, 7)) fan34Owner4Part0)))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000], [285000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([7875000000000], [855000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([4500000000000], [570000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([4125000000000], [1005000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([5130000000000,
      0], [1710000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([6165000000000,
      -9000000000000], [2565000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([4275000000000], [3600000000000]) (some (5, 1, 2)) (some (5, 1, 5)) (.next ([2415000000000,
      -9000000000000], [2715000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([60000000000], [375000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([150000000000],
      [3600000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([60000000000], [4500000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0], [5130000000000]) (some (0, 1, 5)) (some (0, 1,
      5)) (.next ([-285000000000], [3660000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
      ([-855000000000], [8730000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-570000000000],
      [5070000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1005000000000], [5130000000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1710000000000, -9000000000000], [6840000000000,
      9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2565000000000, -9000000000000],
      [8730000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3600000000000], [7875000000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2715000000000, -9000000000000], [5130000000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-375000000000], [435000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([-3600000000000], [3750000000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-4500000000000], [4560000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some
      (0, 2, 5)) (some (0, 2, 5)) (some (0, 2, 5))))))))))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_2 : ExcludedOn (model35.B 2 ++ [step35.q]) 9000000000000 (model35.caps 2)
    (model35.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_3 : ExcludedOn (model35.B 3 ++ [step35.q]) 9000000000000 (model35.caps 3)
    (model35.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_4 : ExcludedOn (model35.B 4 ++ [step35.q]) 9000000000000 (model35.caps 4)
    (model35.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_5 : ExcludedOn (model35.B 5 ++ [step35.q]) 9000000000000 (model35.caps 5)
    (model35.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_6 : ExcludedOn (model35.B 6 ++ [step35.q]) 9000000000000 (model35.caps 6)
    (model35.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5130000000000], [120000000000]) (some (4, 0, 2))
      (some (4, 0, 6)) (.next ([4500000000000], [570000000000]) (some (4, 0, 6)) (some (4, 0, 6))
      (.next ([5130000000000], [1335000000000, 9000000000000]) (some (4, 0, 6)) (some (4, 0, 6))
      (.next ([3750000000000], [1380000000000]) (some (4, 0, 6)) (some (4, 0, 6)) (.next
      ([5130000000000], [3495000000000]) (some (4, 0, 6)) (some (4, 0, 6)) (.next ([2790000000000,
      -9000000000000], [2280000000000, 9000000000000]) (some (4, 0, 6)) (some (4, 0, 6)) (.next
      ([1710000000000, 9000000000000], [1710000000000, 9000000000000]) (some (4, 0, 6)) (some (4, 0,
      6)) (.next ([2040000000000, -9000000000000], [3090000000000, 9000000000000]) (some (4, 0, 6))
      (some (4, 0, 6)) (.next ([1710000000000, 9000000000000], [3870000000000]) (some (4, 0, 6))
      (some (4, 0, 6)) fan35Owner6Part0)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded35_2
    · exact excluded35_3
    · exact excluded35_4
    · exact excluded35_5
    · exact excluded35_6
    · exact excluded35_7
    · exact excluded35_8
    · exact excluded35_9
theorem next35 : model35.insert step35 = model36 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded36_1 : ExcludedOn (model36.B 1 ++ [step36.q]) 9000000000000 (model36.caps 1)
    (model36.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5130000000000, 0], [1710000000000,
      9000000000000]) (some (3, 1, 1)) (some (3, 1, 2)) (.next ([4125000000000], [2160000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2415000000000, -9000000000000], [2160000000000, 0])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2970000000000], [6285000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([0, 0], [1710000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([-1710000000000, -9000000000000], [6840000000000, 9000000000000]) (some (3, 1, 0))
      (some (3, 1, 0)) (.next ([-2160000000000], [6285000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-2160000000000, 0], [4575000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1,
      0)) (.next ([-6285000000000], [9255000000000]) (some (3, 1, 0)) none (.terminal none (some (1,
      1, 3)) none))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded36_2 : ExcludedOn (model36.B 2 ++ [step36.q]) 9000000000000 (model36.caps 2)
    (model36.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7290000000000, -9000000000000], [1710000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2415000000000, -9000000000000],
      [2160000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2160000000000],
      [2715000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([450000000000, -9000000000000],
      [4425000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0],
      [1710000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-1710000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next
      ([-2160000000000, 0], [4575000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-2715000000000], [4875000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-4425000000000, -9000000000000], [4875000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.terminal (some (0, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded36_3 : ExcludedOn (model36.B 3 ++ [step36.q]) 9000000000000 (model36.caps 3)
    (model36.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_4 : ExcludedOn (model36.B 4 ++ [step36.q]) 9000000000000 (model36.caps 4)
    (model36.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_6 : ExcludedOn (model36.B 6 ++ [step36.q]) 9000000000000 (model36.caps 6)
    (model36.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_7 : ExcludedOn (model36.B 7 ++ [step36.q]) 9000000000000 (model36.caps 7)
    (model36.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_8 : ExcludedOn (model36.B 8 ++ [step36.q]) 9000000000000 (model36.caps 8)
    (model36.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_9 : ExcludedOn (model36.B 9 ++ [step36.q]) 9000000000000 (model36.caps 9)
    (model36.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked36 : StepValid model36 9000000000000 step36 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded36_1
    · exact excluded36_2
    · exact excluded36_3
    · exact excluded36_4
    · exact excluded36_5
    · exact excluded36_6
    · exact excluded36_7
    · exact excluded36_8
    · exact excluded36_9
theorem next36 : model36.insert step36 = model37 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint190000200000
end ConwaySoifer.Simplified.Certificates
