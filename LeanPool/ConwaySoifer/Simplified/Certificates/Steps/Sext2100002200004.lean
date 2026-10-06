/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext210000220000
import Mathlib.Tactic.FinCases

/-!
# Sext 210000 220000 4

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
namespace Sext210000220000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan36Owner0Part0 : FanWitness := (.next ([-2415000000000], [9210000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([-705000000000], [2205000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    (.next ([-375000000000], [1005000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([-375000000000], [750000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-2955000000000],
    [5505000000000]) (some (9, 3, 5)) (some (9, 3, 6)) (.next ([-1080000000000], [1830000000000])
    (some (9, 3, 6)) (some (9, 3, 6)) (.next ([-1710000000000], [2835000000000]) (some (9, 3, 6))
    (some (9, 3, 6)) (.next ([-330000000000], [540000000000]) (some (9, 3, 6)) (some (9, 3, 6))
    (.next ([-630000000000], [1005000000000]) (some (9, 3, 6)) (some (9, 4, 6)) (.next
    ([-3705000000000], [5880000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-3960000000000],
    [5880000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-1335000000000], [1830000000000])
    (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-2250000000000], [3045000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) (.next ([-4335000000000], [5505000000000]) (some (9, 4, 6)) (some (9, 4, 6))
    (.next ([-4335000000000], [5250000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([-1380000000000], [1635000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-2715000000000],
    [3210000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-5790000000000], [6630000000000])
    (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-3960000000000], [4500000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) (.next ([-6540000000000], [7005000000000]) (some (9, 4, 6)) (some (9, 4, 6))
    (.next ([-2085000000000], [2205000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([-2340000000000], [2460000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-6000000000000],
    [6300000000000]) (some (9, 4, 6)) (some (9, 4, 9)) (.next ([-6795000000000], [7005000000000])
    (some (9, 4, 9)) (some (9, 4, 9)) (.terminal (some (9, 4, 9)) (some (9, 4, 9)) (some (9, 4,
    9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan36Owner0Part1 : FanWitness := (.next ([795000000000], [2250000000000]) (some (9, 3, 4)) (some
    (9, 3, 4)) (.next ([1170000000000], [4335000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next
    ([915000000000], [4335000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([255000000000],
    [1380000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([495000000000], [2715000000000])
    (some (9, 3, 4)) (some (9, 3, 4)) (.next ([840000000000], [5790000000000]) (some (9, 3, 4))
    (some (9, 3, 4)) (.next ([540000000000], [3960000000000]) (some (9, 3, 4)) (some (9, 3, 4))
    (.next ([465000000000], [6540000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next
    ([120000000000], [2085000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([120000000000],
    [2340000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([300000000000], [6000000000000])
    (some (9, 3, 4)) (some (9, 3, 4)) (.next ([210000000000], [6795000000000]) (some (9, 3, 4))
    (some (9, 3, 5)) (.next ([0], [255000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([-75000000000], [6750000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-165000000000],
    [6165000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-330000000000], [7005000000000])
    (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-540000000000], [7170000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([-795000000000], [7170000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    (.next ([-1080000000000], [7380000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([-255000000000], [1635000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-1170000000000],
    [6795000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-1335000000000], [7380000000000])
    (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-1875000000000], [9000000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([-1710000000000], [7005000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    fan36Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner0Part0 : FanWitness := (.next ([-1710000000000], [7005000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([-2388000000000], [8388000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    (.next ([-2928000000000], [8598000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([-630000000000], [1848000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-1005000000000],
    [2853000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-375000000000], [1005000000000])
    (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-1005000000000], [2598000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([-375000000000], [750000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    (.next ([-2955000000000], [5505000000000]) (some (9, 3, 5)) (some (9, 3, 6)) (.next
    ([-1710000000000], [2835000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([-330000000000],
    [540000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([-630000000000], [1005000000000])
    (some (9, 3, 6)) (some (9, 4, 6)) (.next ([-3705000000000], [5880000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) (.next ([-3960000000000], [5880000000000]) (some (9, 4, 6)) (some (9, 4, 6))
    (.next ([-2250000000000], [3045000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([-1218000000000], [1593000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-4335000000000],
    [5505000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-4335000000000], [5250000000000])
    (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-1380000000000], [1635000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) (.next ([-5790000000000], [6630000000000]) (some (9, 4, 6)) (some (9, 4, 6))
    (.next ([-3960000000000], [4500000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([-6540000000000], [7005000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-6000000000000],
    [6300000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-6795000000000], [7005000000000])
    (some (9, 4, 6)) (some (9, 4, 6)) (.terminal (some (9, 4, 6)) (some (9, 4, 6)) (some (9, 4,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner0Part1 : FanWitness := (.next ([2175000000000], [3705000000000]) (some (9, 3, 4))
    (some (9, 3, 4)) (.next ([1920000000000], [3960000000000]) (some (9, 3, 4)) (some (9, 3, 4))
    (.next ([795000000000], [2250000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next
    ([375000000000], [1218000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([1170000000000],
    [4335000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([915000000000], [4335000000000])
    (some (9, 3, 4)) (some (9, 3, 4)) (.next ([255000000000], [1380000000000]) (some (9, 3, 4))
    (some (9, 3, 4)) (.next ([840000000000], [5790000000000]) (some (9, 3, 4)) (some (9, 3, 4))
    (.next ([540000000000], [3960000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next
    ([465000000000], [6540000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([300000000000],
    [6000000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([210000000000], [6795000000000])
    (some (9, 3, 4)) (some (9, 3, 5)) (.next ([0], [255000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    (.next ([-75000000000], [6750000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([-330000000000], [7005000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-540000000000],
    [7170000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-795000000000], [7170000000000])
    (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-678000000000], [5553000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([-1080000000000], [7380000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    (.next ([-255000000000], [1635000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([-1170000000000], [6795000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-1335000000000],
    [7380000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-630000000000], [3228000000000])
    (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-375000000000], [1593000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) fan37Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner5Part0 : FanWitness := (.next ([5250000000000], [348000000000]) (some (5, 1, 2)) (some
    (5, 1, 2)) (.next ([6027000000000], [453000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([6777000000000], [2223000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([348000000000],
    [267000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2520000000000], [5115000000000])
    (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2172000000000], [4848000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([750000000000], [1770000000000]) (some (5, 1, 2)) (some (5, 1, 2))
    (.next ([1890000000000, 9000000000000], [5865000000000, 0]) (some (5, 1, 2)) (some (5, 1, 2))
    (.next ([1542000000000, 9000000000000], [5598000000000, 0]) (some (5, 1, 2)) (some (5, 1, 2))
    (.next ([1179000000000], [7473000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([912000000000], [8088000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([0, 0],
    [1890000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 5)) (.next ([-333000000000,
    9000000000000], [7110000000000, -9000000000000]) (some (5, 1, 5)) (some (5, 2, 5)) (.next
    ([-348000000000], [5598000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-453000000000],
    [6480000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2223000000000], [9000000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-267000000000], [615000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-5115000000000], [7635000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-4848000000000], [7020000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1770000000000], [2520000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5865000000000,
    0], [7755000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5598000000000,
    0], [7140000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-7473000000000],
    [8652000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-8088000000000], [9000000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan39Owner1Part0 : FanWitness := (.next ([3420000000000, 9000000000000], [360000000000,
    -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([7110000000000], [1305000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([5850000000000], [1260000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([2835000000000], [990000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([1890000000000, 9000000000000], [1890000000000, 9000000000000]) (some (0, 5, 3)) (some
    (0, 5, 3)) (.next ([945000000000, -9000000000000], [990000000000, 0]) (some (0, 5, 3)) (some (0,
    5, 3)) (.next ([2520000000000], [3690000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([1530000000000], [2250000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([2520000000000], [5580000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([900000000000,
    9000000000000], [3825000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([630000000000,
    -9000000000000], [7470000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0],
    [1890000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-45000000000],
    [1305000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next ([-360000000000, 9000000000000],
    [3780000000000]) (some (0, 5, 4)) (some (1, 5, 4)) (.next ([-1305000000000], [8415000000000])
    (some (1, 5, 4)) none (.next ([-1260000000000], [7110000000000]) none none (.next
    ([-990000000000], [3825000000000]) none none (.next ([-1890000000000, -9000000000000],
    [3780000000000, 18000000000000]) none none (.next ([-990000000000, 0], [1935000000000,
    -9000000000000]) none none (.next ([-3690000000000, 9000000000000], [6210000000000,
    -9000000000000]) none none (.next ([-2250000000000], [3780000000000]) (some (5, 2, 0)) (some (5,
    2, 0)) (.next ([-5580000000000], [8100000000000]) (some (5, 2, 0)) (some (5, 2, 0)) (.next
    ([-3825000000000], [4725000000000, 9000000000000]) (some (5, 2, 0)) (some (5, 2, 0)) (.next
    ([-7470000000000, -9000000000000], [8100000000000, 0]) (some (5, 2, 0)) (some (5, 2, 0))
    (.terminal (some (5, 2, 0)) (some (5, 2, 0)) (some (5, 2, 0)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_1 : ExcludedOn (model32.B 1 ++ [step32.q]) 9000000000000 (model32.caps 1)
    (model32.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_2 : ExcludedOn (model32.B 2 ++ [step32.q]) 9000000000000 (model32.caps 2)
    (model32.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_4 : ExcludedOn (model32.B 4 ++ [step32.q]) 9000000000000 (model32.caps 4)
    (model32.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4485000000000], [765000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([4005000000000], [870000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([2520000000000, 9000000000000], [2730000000000, -9000000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([3855000000000], [4545000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([2040000000000, 9000000000000], [2835000000000, -9000000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([1890000000000, 9000000000000], [4545000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([105000000000], [375000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([705000000000], [3915000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next
      ([630000000000], [4620000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([330000000000],
      [4395000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([150000000000], [4725000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([0], [4545000000000]) (some (5, 1, 3)) (some (5, 1,
      3)) (.next ([-765000000000], [5250000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-870000000000], [4875000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2730000000000,
      9000000000000], [5250000000000]) (some (0, 1, 3)) (some (0, 1, 5)) (.next ([-4545000000000],
      [8400000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2835000000000, 9000000000000],
      [4875000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4545000000000], [6435000000000,
      9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-375000000000], [480000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3915000000000], [4620000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([-4620000000000], [5250000000000]) (some (0, 1, 5)) (some (0, 2, 5))
      (.next ([-4395000000000], [4725000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-4725000000000], [4875000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2,
      5)) (some (0, 2, 5)) (some (0, 2, 5))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded32_5 : ExcludedOn (model32.B 5 ++ [step32.q]) 9000000000000 (model32.caps 5)
    (model32.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_6 : ExcludedOn (model32.B 6 ++ [step32.q]) 9000000000000 (model32.caps 6)
    (model32.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_7 : ExcludedOn (model32.B 7 ++ [step32.q]) 9000000000000 (model32.caps 7)
    (model32.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_8 : ExcludedOn (model32.B 8 ++ [step32.q]) 9000000000000 (model32.caps 8)
    (model32.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3600000000000], [1545000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([5145000000000], [3855000000000]) (some (0, 1, 2)) (some (0, 1,
      2)) (.next ([2430000000000], [5025000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([120000000000], [3855000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [5025000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.next ([-1545000000000], [5145000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-3855000000000], [9000000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-5025000000000], [7455000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-3855000000000], [3975000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded32_9 : ExcludedOn (model32.B 9 ++ [step32.q]) 9000000000000 (model32.caps 9)
    (model32.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded32_4
    · exact excluded32_5
    · exact excluded32_6
    · exact excluded32_7
    · exact excluded32_8
    · exact excluded32_9
theorem next32 : model32.insert step32 = model33 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded33_0 : ExcludedOn (model33.B 0 ++ [step33.q]) 9000000000000 (model33.caps 0)
    (model33.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_1 : ExcludedOn (model33.B 1 ++ [step33.q]) 9000000000000 (model33.caps 1)
    (model33.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_3 : ExcludedOn (model33.B 3 ++ [step33.q]) 9000000000000 (model33.caps 3)
    (model33.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3105000000000], [3780000000000]) (some (2, 0,
      1)) (some (3, 0, 1)) (.next ([3105000000000], [5145000000000]) (some (3, 0, 1)) (some (3, 0,
      4)) (.next ([1890000000000, 9000000000000], [4995000000000, -9000000000000]) (some (3, 0, 4))
      (some (3, 0, 4)) (.next ([1890000000000, 9000000000000], [5145000000000]) (some (3, 0, 4))
      (some (3, 0, 4)) (.next ([1740000000000], [5145000000000]) (some (3, 0, 4)) (some (3, 0, 4))
      (.next ([0], [5145000000000]) (some (3, 0, 4)) (some (3, 1, 4)) (.next ([-3780000000000],
      [6885000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-5145000000000], [8250000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-4995000000000, 9000000000000], [6885000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-5145000000000, 0], [7035000000000, 9000000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-5145000000000], [6885000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.terminal (some (0, 1, 4)) (some (0, 1, 2)) (some (0, 1, 4)))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_7 : ExcludedOn (model33.B 7 ++ [step33.q]) 9000000000000 (model33.caps 7)
    (model33.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_8 : ExcludedOn (model33.B 8 ++ [step33.q]) 9000000000000 (model33.caps 8)
    (model33.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_9 : ExcludedOn (model33.B 9 ++ [step33.q]) 9000000000000 (model33.caps 9)
    (model33.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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

theorem excluded34_0 : ExcludedOn (model34.B 0 ++ [step34.q]) 9000000000000 (model34.caps 0)
    (model34.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_1 : ExcludedOn (model34.B 1 ++ [step34.q]) 9000000000000 (model34.caps 1)
    (model34.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_3 : ExcludedOn (model34.B 3 ++ [step34.q]) 9000000000000 (model34.caps 3)
    (model34.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3510000000000], [225000000000]) (some (2, 0, 1))
      (some (3, 0, 1)) (.next ([5625000000000, 9000000000000], [1485000000000, -9000000000000])
      (some (3, 0, 1)) (some (3, 0, 1)) (.next ([1965000000000], [1410000000000]) (some (3, 0, 1))
      (some (3, 0, 1)) (.next ([3735000000000], [3375000000000]) (some (3, 0, 1)) (some (3, 4, 1))
      (.next ([1890000000000, 9000000000000], [4995000000000, -9000000000000]) (some (3, 4, 1))
      (some (3, 4, 1)) (.next ([1890000000000, 9000000000000], [5145000000000]) (some (3, 4, 1))
      (some (3, 4, 2)) (.next ([1740000000000], [5145000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([0], [5145000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-225000000000],
      [3735000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1485000000000, 9000000000000],
      [7110000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1410000000000], [3375000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3375000000000], [7110000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-4995000000000, 9000000000000], [6885000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-5145000000000, 0], [7035000000000, 9000000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-5145000000000], [6885000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.terminal (some (0, 1, 2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_7 : ExcludedOn (model34.B 7 ++ [step34.q]) 9000000000000 (model34.caps 7)
    (model34.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded34_0
    · exact excluded34_1
    · exact excluded34_2
    · exact excluded34_3
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 3 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_1 : ExcludedOn (model35.B 1 ++ [step35.q]) 9000000000000 (model35.caps 1)
    (model35.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_3 : ExcludedOn (model35.B 3 ++ [step35.q]) 9000000000000 (model35.caps 3)
    (model35.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3780000000000, 0], [328500000000,
      -9000000000000]) (some (2, 0, 1)) (some (3, 0, 1)) (.next ([5998500000000], [1365000000000])
      (some (3, 0, 1)) (some (3, 0, 1)) (.next ([2218500000000], [886500000000]) (some (3, 0, 1))
      (some (3, 0, 1)) (.next ([3780000000000], [2218500000000]) (some (3, 0, 1)) (some (3, 0, 4))
      (.next ([1890000000000, 9000000000000], [4995000000000, -9000000000000]) (some (3, 0, 4))
      (some (3, 0, 4)) (.next ([1890000000000, 9000000000000], [5145000000000]) (some (3, 0, 4))
      (some (3, 0, 4)) (.next ([1740000000000], [5145000000000]) (some (3, 0, 4)) (some (3, 0, 4))
      (.next ([0], [5145000000000]) (some (3, 0, 4)) (some (3, 1, 4)) (.next ([-328500000000,
      9000000000000], [4108500000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-1365000000000], [7363500000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-886500000000],
      [3105000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2218500000000], [5998500000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4995000000000, 9000000000000], [6885000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5145000000000, 0], [7035000000000, 9000000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5145000000000], [6885000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1, 2)) (some (0, 1,
      2))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded35_4 : ExcludedOn (model35.B 4 ++ [step35.q]) 9000000000000 (model35.caps 4)
    (model35.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_5 : ExcludedOn (model35.B 5 ++ [step35.q]) 9000000000000 (model35.caps 5)
    (model35.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_6 : ExcludedOn (model35.B 6 ++ [step35.q]) 9000000000000 (model35.caps 6)
    (model35.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_7 : ExcludedOn (model35.B 7 ++ [step35.q]) 9000000000000 (model35.caps 7)
    (model35.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_8 : ExcludedOn (model35.B 8 ++ [step35.q]) 9000000000000 (model35.caps 8)
    (model35.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_9 : ExcludedOn (model35.B 9 ++ [step35.q]) 9000000000000 (model35.caps 9)
    (model35.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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

theorem excluded36_0 : ExcludedOn (model36.B 0 ++ [step36.q]) 9000000000000 (model36.caps 0)
    (model36.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6675000000000], [75000000000]) (some (9, 9, 4))
      (some (9, 9, 4)) (.next ([6000000000000], [165000000000]) (some (9, 9, 4)) (some (9, 9, 4))
      (.next ([6675000000000], [330000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next
      ([6630000000000], [540000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next ([6375000000000],
      [795000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next ([6300000000000], [1080000000000])
      (some (9, 2, 4)) (some (9, 2, 4)) (.next ([1380000000000], [255000000000]) (some (9, 2, 4))
      (some (9, 2, 4)) (.next ([5625000000000], [1170000000000]) (some (9, 2, 4)) (some (9, 2, 4))
      (.next ([6045000000000], [1335000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next
      ([7125000000000], [1875000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next ([5295000000000],
      [1710000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next ([6795000000000], [2415000000000])
      (some (9, 2, 4)) (some (9, 2, 4)) (.next ([1500000000000], [705000000000]) (some (9, 2, 4))
      (some (9, 2, 4)) (.next ([630000000000], [375000000000]) (some (9, 2, 4)) (some (9, 2, 4))
      (.next ([375000000000], [375000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next
      ([2550000000000], [2955000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next ([750000000000],
      [1080000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next ([1125000000000], [1710000000000])
      (some (9, 2, 4)) (some (9, 2, 4)) (.next ([210000000000], [330000000000]) (some (9, 2, 4))
      (some (9, 3, 4)) (.next ([375000000000], [630000000000]) (some (9, 3, 4)) (some (9, 3, 4))
      (.next ([2175000000000], [3705000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next
      ([1920000000000], [3960000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([495000000000],
      [1335000000000]) (some (9, 3, 4)) (some (9, 3, 4)) fan36Owner0Part1))))))))))))))))))))))))
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded36_1 : ExcludedOn (model36.B 1 ++ [step36.q]) 9000000000000 (model36.caps 1)
    (model36.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_2 : ExcludedOn (model36.B 2 ++ [step36.q]) 9000000000000 (model36.caps 2)
    (model36.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_3 : ExcludedOn (model36.B 3 ++ [step36.q]) 9000000000000 (model36.caps 3)
    (model36.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3600000000000, 9000000000000], [4275000000000,
      -9000000000000]) (some (2, 0, 1)) (some (3, 0, 1)) (.next ([2730000000000], [3435000000000])
      (some (3, 0, 1)) (some (3, 0, 1)) (.next ([720000000000], [990000000000]) (some (3, 0, 1))
      (some (3, 4, 1)) (.next ([1890000000000, 9000000000000], [4995000000000, -9000000000000])
      (some (3, 4, 1)) (some (3, 4, 1)) (.next ([1890000000000, 9000000000000], [5145000000000])
      (some (3, 4, 1)) (some (3, 4, 2)) (.next ([1740000000000], [5145000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([1710000000000], [6165000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([0], [5145000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-4275000000000,
      9000000000000], [7875000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-3435000000000],
      [6165000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-990000000000], [1710000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4995000000000, 9000000000000], [6885000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5145000000000, 0], [7035000000000, 9000000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5145000000000], [6885000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-6165000000000], [7875000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.terminal (some (0, 1, 2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_6 : ExcludedOn (model36.B 6 ++ [step36.q]) 9000000000000 (model36.caps 6)
    (model36.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_7 : ExcludedOn (model36.B 7 ++ [step36.q]) 9000000000000 (model36.caps 7)
    (model36.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_8 : ExcludedOn (model36.B 8 ++ [step36.q]) 9000000000000 (model36.caps 8)
    (model36.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_9 : ExcludedOn (model36.B 9 ++ [step36.q]) 9000000000000 (model36.caps 9)
    (model36.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded36_5
    · exact excluded36_6
    · exact excluded36_7
    · exact excluded36_8
    · exact excluded36_9
theorem next36 : model36.insert step36 = model37 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded37_0 : ExcludedOn (model37.B 0 ++ [step37.q]) 9000000000000 (model37.caps 0)
    (model37.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6675000000000], [75000000000]) (some (6, 9, 4))
      (some (7, 9, 4)) (.next ([6675000000000], [330000000000]) (some (7, 9, 4)) (some (7, 9, 4))
      (.next ([6630000000000], [540000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next
      ([6375000000000], [795000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next ([4875000000000],
      [678000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next ([6300000000000], [1080000000000])
      (some (7, 2, 4)) (some (7, 2, 4)) (.next ([1380000000000], [255000000000]) (some (7, 2, 4))
      (some (7, 2, 4)) (.next ([5625000000000], [1170000000000]) (some (7, 2, 4)) (some (7, 2, 4))
      (.next ([6045000000000], [1335000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next
      ([2598000000000], [630000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([1218000000000],
      [375000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([5295000000000], [1710000000000])
      (some (7, 2, 4)) (some (7, 2, 4)) (.next ([6000000000000], [2388000000000]) (some (7, 2, 4))
      (some (7, 2, 4)) (.next ([5670000000000], [2928000000000]) (some (7, 2, 4)) (some (7, 2, 4))
      (.next ([1218000000000], [630000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next
      ([1848000000000], [1005000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([630000000000],
      [375000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([1593000000000], [1005000000000])
      (some (7, 2, 4)) (some (7, 2, 4)) (.next ([375000000000], [375000000000]) (some (7, 2, 4))
      (some (9, 2, 4)) (.next ([2550000000000], [2955000000000]) (some (9, 2, 4)) (some (9, 2, 4))
      (.next ([1125000000000], [1710000000000]) (some (9, 2, 4)) (some (9, 2, 4)) (.next
      ([210000000000], [330000000000]) (some (9, 2, 4)) (some (9, 3, 4)) (.next ([375000000000],
      [630000000000]) (some (9, 3, 4)) (some (9, 3, 4)) fan37Owner0Part1))))))))))))))))))))))))
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_1 : ExcludedOn (model37.B 1 ++ [step37.q]) 9000000000000 (model37.caps 1)
    (model37.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_2 : ExcludedOn (model37.B 2 ++ [step37.q]) 9000000000000 (model37.caps 2)
    (model37.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_3 : ExcludedOn (model37.B 3 ++ [step37.q]) 9000000000000 (model37.caps 3)
    (model37.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3855000000000], [2922000000000]) (some (2, 0,
      1)) (some (3, 0, 1)) (.next ([4113000000000, 9000000000000], [4887000000000, -9000000000000])
      (some (3, 0, 1)) (some (3, 4, 1)) (.next ([1890000000000, 9000000000000], [4995000000000,
      -9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([1890000000000, 9000000000000],
      [5145000000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next ([1740000000000], [5145000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([2223000000000], [6777000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([108000000000], [2115000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([0], [5145000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-2922000000000],
      [6777000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4887000000000, 9000000000000],
      [9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4995000000000, 9000000000000],
      [6885000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-5145000000000, 0],
      [7035000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-5145000000000],
      [6885000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-6777000000000], [9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2115000000000], [2223000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.terminal (some (0, 1, 2)) (some (0, 1, 2)) (some (0, 1,
      2))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded37_5 : ExcludedOn (model37.B 5 ++ [step37.q]) 9000000000000 (model37.caps 5)
    (model37.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6777000000000, 0], [333000000000,
      -9000000000000]) (some (5, 0, 2)) (some (5, 1, 2)) fan37Owner5Part0)) (den := 9000000000000)
      (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_6 : ExcludedOn (model37.B 6 ++ [step37.q]) 9000000000000 (model37.caps 6)
    (model37.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_7 : ExcludedOn (model37.B 7 ++ [step37.q]) 9000000000000 (model37.caps 7)
    (model37.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded37_1
    · exact excluded37_2
    · exact excluded37_3
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 3 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_1 : ExcludedOn (model38.B 1 ++ [step38.q]) 9000000000000 (model38.caps 1)
    (model38.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_3 : ExcludedOn (model38.B 3 ++ [step38.q]) 9000000000000 (model38.caps 3)
    (model38.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7110000000000], [270000000000]) (some (2, 0, 4))
      (some (3, 0, 4)) (.next ([4875000000000, 0], [345000000000, -9000000000000]) (some (3, 0, 4))
      (some (3, 0, 4)) (.next ([4875000000000], [2235000000000]) (some (3, 0, 4)) (some (3, 0, 4))
      (.next ([1890000000000, 9000000000000], [4995000000000, -9000000000000]) (some (3, 0, 4))
      (some (3, 0, 4)) (.next ([1890000000000, 9000000000000], [5145000000000]) (some (3, 0, 4))
      (some (3, 0, 4)) (.next ([1740000000000], [5145000000000]) (some (3, 0, 4)) (some (3, 0, 4))
      (.next ([225000000000], [2010000000000]) (some (3, 0, 4)) (some (3, 1, 4)) (.next ([0],
      [5145000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([-270000000000], [7380000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-345000000000, 9000000000000], [5220000000000,
      -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2235000000000], [7110000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4995000000000, 9000000000000], [6885000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5145000000000, 0], [7035000000000, 9000000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5145000000000], [6885000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-2010000000000], [2235000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.terminal (some (0, 1, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded38_4 : ExcludedOn (model38.B 4 ++ [step38.q]) 9000000000000 (model38.caps 4)
    (model38.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_5 : ExcludedOn (model38.B 5 ++ [step38.q]) 9000000000000 (model38.caps 5)
    (model38.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_6 : ExcludedOn (model38.B 6 ++ [step38.q]) 9000000000000 (model38.caps 6)
    (model38.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_7 : ExcludedOn (model38.B 7 ++ [step38.q]) 9000000000000 (model38.caps 7)
    (model38.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded38_0
    · exact excluded38_1
    · exact (hj rfl).elim
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

theorem excluded39_1 : ExcludedOn (model39.B 1 ++ [step39.q]) 9000000000000 (model39.caps 1)
    (model39.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1260000000000], [45000000000]) (some (0, 5, 2))
      (some (0, 5, 3)) fan39Owner1Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded39_2 : ExcludedOn (model39.B 2 ++ [step39.q]) 9000000000000 (model39.caps 2)
    (model39.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_3 : ExcludedOn (model39.B 3 ++ [step39.q]) 9000000000000 (model39.caps 3)
    (model39.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_4 : ExcludedOn (model39.B 4 ++ [step39.q]) 9000000000000 (model39.caps 4)
    (model39.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_5 : ExcludedOn (model39.B 5 ++ [step39.q]) 9000000000000 (model39.caps 5)
    (model39.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_6 : ExcludedOn (model39.B 6 ++ [step39.q]) 9000000000000 (model39.caps 6)
    (model39.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2790000000000, 9000000000000], [630000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([2520000000000], [3690000000000,
      -9000000000000]) (some (2, 0, 2)) (some (2, 0, 2)) (.next ([900000000000], [2520000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([1890000000000, 9000000000000], [7110000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1890000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-630000000000, 9000000000000],
      [3420000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-3690000000000, 9000000000000],
      [6210000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2520000000000],
      [3420000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-7110000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_7 : ExcludedOn (model39.B 7 ++ [step39.q]) 9000000000000 (model39.caps 7)
    (model39.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_8 : ExcludedOn (model39.B 8 ++ [step39.q]) 9000000000000 (model39.caps 8)
    (model39.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_9 : ExcludedOn (model39.B 9 ++ [step39.q]) 9000000000000 (model39.caps 9)
    (model39.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked39 : StepValid model39 9000000000000 step39 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded39_1
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

end Sext210000220000
end ConwaySoifer.Simplified.Certificates
