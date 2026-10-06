/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint340000350000
import Mathlib.Tactic.FinCases

/-!
# Sint 340000 350000 4

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
namespace Sint340000350000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner5Part0 : FanWitness := (.next ([3495000000000], [3825000000000]) (some (6, 1, 4))
    (some (6, 1, 4)) (.next ([2673000000000], [3375000000000]) (some (6, 1, 4)) (some (6, 1, 4))
    (.next ([2340000000000], [3240000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
    ([1350000000000], [3750000000000]) (some (6, 1, 4)) (some (6, 1, 5)) (.next ([330000000000],
    [1020000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([180000000000, -9000000000000],
    [585000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0], [4080000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-117000000000], [3492000000000]) (some (0, 1, 5)) (some (0, 2, 5))
    (.next ([-585000000000], [3825000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1065000000000], [4815000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1710000000000,
    -9000000000000], [6810000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-135000000000], [468000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2142000000000],
    [7125000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2085000000000], [6165000000000])
    (some (0, 2, 5)) (some (0, 3, 5)) (.next ([-2475000000000], [6990000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([-3060000000000, -9000000000000], [7140000000000, 9000000000000]) (some
    (0, 3, 5)) (some (0, 3, 5)) (.next ([-3492000000000], [7455000000000]) (some (0, 3, 5)) (some
    (0, 3, 5)) (.next ([-3060000000000, -9000000000000], [6165000000000]) (some (0, 3, 5)) (some (0,
    3, 5)) (.next ([-3825000000000], [7320000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([-3375000000000], [6048000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-3240000000000],
    [5580000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-3750000000000], [5100000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-1020000000000], [1350000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([-585000000000, 0], [765000000000, -9000000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.terminal (some (0, 3, 5)) (some (0, 3, 5)) (some (0, 3,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner5Part0 : FanWitness := (.next ([3105000000000, -9000000000000], [3060000000000,
    9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3495000000000], [3825000000000])
    (some (6, 1, 4)) (some (6, 1, 4)) (.next ([2673000000000], [3375000000000]) (some (6, 1, 4))
    (some (6, 1, 4)) (.next ([2340000000000], [3240000000000]) (some (6, 1, 4)) (some (6, 1, 4))
    (.next ([1875000000000], [3492000000000]) (some (6, 1, 4)) (some (6, 1, 5)) (.next
    ([588000000000], [1287000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([180000000000,
    -9000000000000], [585000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0], [4080000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-117000000000], [3492000000000]) (some (0, 1, 5))
    (some (0, 2, 5)) (.next ([-585000000000], [3825000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-798000000000], [4290000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1617000000000], [6867000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-135000000000],
    [468000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1950000000000], [6732000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2085000000000], [6165000000000]) (some (0, 2, 5))
    (some (0, 3, 5)) (.next ([-3060000000000, -9000000000000], [7140000000000, 9000000000000]) (some
    (0, 3, 5)) (some (0, 3, 5)) (.next ([-3492000000000], [7455000000000]) (some (0, 3, 5)) (some
    (0, 3, 5)) (.next ([-3060000000000, -9000000000000], [6165000000000]) (some (0, 3, 5)) (some (0,
    3, 5)) (.next ([-3825000000000], [7320000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([-3375000000000], [6048000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-3240000000000],
    [5580000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-3492000000000], [5367000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-1287000000000], [1875000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([-585000000000, 0], [765000000000, -9000000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.terminal (some (0, 3, 5)) (some (0, 3, 5)) (some (0, 3,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner3Part0 : FanWitness := (.next ([135000000000], [4365000000000]) (some (6, 1, 5)) (some
    (6, 1, 5)) (.next ([0], [3060000000000, 9000000000000]) (some (6, 1, 5)) (some (6, 7, 5)) (.next
    ([-1125000000000], [5760000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-1290000000000],
    [4635000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-1260000000000], [4500000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-1350000000000], [4500000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-1305000000000], [4260000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-1350000000000], [3885000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-2685000000000, -9000000000000], [7140000000000, 9000000000000]) (some (0, 7, 5)) (some (0, 7,
    5)) (.next ([-3060000000000, -9000000000000], [7530000000000, 9000000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-3750000000000], [6900000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-3750000000000], [6810000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-4125000000000], [7320000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-4125000000000],
    [7230000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-4500000000000], [7710000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-4500000000000], [7620000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-4185000000000, -9000000000000], [5760000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-3660000000000], [4410000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-375000000000], [420000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-4080000000000], [4455000000000]) (some (0, 7, 5)) (some (1, 7, 5)) (.next ([-750000000000],
    [810000000000]) (some (1, 7, 5)) (some (1, 7, 5)) (.next ([-375000000000], [390000000000]) (some
    (1, 7, 5)) (some (1, 7, 5)) (.next ([-4275000000000], [4410000000000]) (some (1, 7, 5)) (some
    (1, 7, 5)) (.next ([-4365000000000], [4500000000000]) (some (1, 7, 5)) (some (1, 7, 5))
    (.terminal (some (1, 7, 5)) (some (1, 7, 5)) (some (1, 7, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner3Part0 : FanWitness := (.next ([0], [3060000000000, 9000000000000]) (some (6, 7, 5))
    (some (6, 7, 5)) (.next ([-1065000000000], [9000000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-1080000000000], [8625000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-1125000000000], [8250000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-1260000000000],
    [4500000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-1350000000000], [4500000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-2310000000000, -9000000000000], [6720000000000,
    9000000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-2685000000000, -9000000000000],
    [7140000000000, 9000000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-3060000000000,
    -9000000000000], [7530000000000, 9000000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-3750000000000], [6900000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-3750000000000],
    [6810000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-4125000000000], [7320000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-4125000000000], [7230000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-4500000000000], [7710000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-4500000000000], [7620000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-5535000000000], [9000000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-3660000000000],
    [4410000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-375000000000], [420000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-4080000000000], [4455000000000]) (some (0, 7, 5))
    (some (1, 7, 5)) (.next ([-750000000000], [810000000000]) (some (1, 7, 5)) (some (1, 7, 5))
    (.next ([-4185000000000], [4500000000000]) (some (1, 7, 5)) (some (1, 7, 5)) (.next
    ([-5535000000000], [5940000000000, -9000000000000]) (some (1, 7, 5)) (some (1, 7, 5)) (.next
    ([-4275000000000], [4500000000000]) (some (1, 7, 5)) (some (1, 7, 5)) (.next ([-375000000000],
    [390000000000]) (some (1, 7, 5)) (some (7, 7, 5)) (.terminal (some (7, 7, 5)) (some (7, 7, 5))
    (some (7, 7, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner4Part0 : FanWitness := (.next ([-1350000000000], [5250000000000]) (some (0, 2, 8))
    (some (0, 2, 8)) (.next ([-1122000000000], [3750000000000]) (some (0, 2, 8)) (some (0, 2, 8))
    (.next ([-1173000000000], [3633000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next
    ([-1875000000000], [5508000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-585000000000],
    [1620000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-2055000000000], [5535000000000])
    (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-1872000000000], [4500000000000]) (some (0, 2, 7))
    (some (0, 2, 7)) (.next ([-3492000000000], [6972000000000]) (some (0, 2, 7)) (some (0, 2, 7))
    (.next ([-267000000000], [525000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
    ([-3750000000000], [6120000000000]) (some (0, 2, 7)) (some (0, 3, 7)) (.next ([-3492000000000],
    [5535000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-1530000000000], [2400000000000])
    (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-1263000000000], [1875000000000]) (some (0, 3, 7))
    (some (0, 3, 7)) (.next ([-5250000000000], [7380000000000]) (some (0, 3, 7)) (some (0, 4, 7))
    (.next ([-2280000000000], [3150000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next
    ([-4500000000000], [6120000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next ([-1785000000000],
    [2370000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next ([-2013000000000], [2625000000000])
    (some (0, 4, 7)) (some (0, 4, 7)) (.next ([-1350000000000], [1758000000000]) (some (0, 4, 7))
    (some (0, 4, 7)) (.next ([-5508000000000], [7113000000000]) (some (0, 4, 7)) (some (0, 4, 7))
    (.next ([-3492000000000], [4335000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next
    ([-1875000000000], [2016000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next ([-3900000000000],
    [4185000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next ([-3633000000000], [3660000000000])
    (some (0, 4, 7)) (some (0, 4, 7)) (.terminal (some (0, 4, 7)) (some (0, 4, 7)) (some (0, 4,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner4Part1 : FanWitness := (.next ([3480000000000], [3492000000000]) (some (7, 1, 8))
    (some (7, 1, 8)) (.next ([258000000000], [267000000000]) (some (7, 1, 8)) (some (7, 1, 8))
    (.next ([2370000000000], [3750000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next
    ([2043000000000], [3492000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([870000000000],
    [1530000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([612000000000], [1263000000000])
    (some (7, 1, 8)) (some (7, 1, 8)) (.next ([2130000000000], [5250000000000]) (some (7, 1, 8))
    (some (7, 1, 8)) (.next ([870000000000], [2280000000000]) (some (7, 1, 8)) (some (7, 1, 8))
    (.next ([1620000000000], [4500000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next
    ([585000000000], [1785000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([612000000000],
    [2013000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([408000000000], [1350000000000])
    (some (7, 1, 8)) (some (7, 1, 8)) (.next ([1605000000000], [5508000000000]) (some (7, 1, 8))
    (some (7, 2, 8)) (.next ([843000000000], [3492000000000]) (some (7, 2, 8)) (some (7, 2, 8))
    (.next ([141000000000], [1875000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
    ([285000000000], [3900000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([27000000000],
    [3633000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([0], [3492000000000]) (some (7, 2,
    8)) (some (7, 2, 8)) (.next ([-270000000000], [6120000000000]) (some (0, 2, 8)) (some (0, 2, 8))
    (.next ([-165000000000], [1785000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next
    ([-1020000000000], [6120000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-855000000000],
    [4335000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-915000000000], [3900000000000])
    (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-585000000000], [2370000000000]) (some (0, 2, 8))
    (some (0, 2, 8)) fan35Owner4Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner5Part0 : FanWitness := (.next ([3495000000000], [3825000000000]) (some (6, 1, 4))
    (some (6, 1, 4)) (.next ([2673000000000], [3375000000000]) (some (6, 1, 4)) (some (6, 1, 4))
    (.next ([2340000000000], [3240000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
    ([2475000000000, -9000000000000], [6525000000000, 9000000000000]) (some (6, 1, 4)) (some (6, 1,
    5)) (.next ([2043000000000], [6840000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next
    ([1710000000000], [6705000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([615000000000],
    [4920000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([0], [4080000000000]) (some (0, 1,
    5)) (some (0, 1, 5)) (.next ([-117000000000], [3492000000000]) (some (0, 1, 5)) (some (0, 2, 5))
    (.next ([-585000000000], [3825000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-630000000000], [3465000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-135000000000],
    [468000000000]) (some (0, 2, 5)) (some (0, 2, 6)) (.next ([-2085000000000], [6165000000000])
    (some (0, 2, 6)) (some (0, 3, 6)) (.next ([-3465000000000], [9000000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-3060000000000, -9000000000000], [7140000000000, 9000000000000]) (some
    (0, 3, 6)) (some (0, 3, 6)) (.next ([-3492000000000], [7455000000000]) (some (0, 3, 6)) (some
    (0, 3, 6)) (.next ([-3060000000000, -9000000000000], [6165000000000]) (some (0, 3, 6)) (some (0,
    3, 6)) (.next ([-3825000000000], [7320000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-3375000000000], [6048000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-3240000000000],
    [5580000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-6525000000000, -9000000000000],
    [9000000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-6840000000000], [8883000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-6705000000000], [8415000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-4920000000000], [5535000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.terminal (some (0, 3, 6)) (some (0, 3, 6)) (some (0, 3, 6)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 3 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_5 : ExcludedOn (model32.B 5 ++ [step32.q]) 9000000000000 (model32.caps 5)
    (model32.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000], [117000000000]) (some (5, 0, 3))
      (some (5, 1, 3)) (.next ([3240000000000], [585000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([3750000000000], [1065000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([5100000000000, 0], [1710000000000, 9000000000000]) (some (5, 1, 3)) (some (6, 1, 3)) (.next
      ([333000000000], [135000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4983000000000],
      [2142000000000]) (some (6, 1, 3)) (some (6, 1, 4)) (.next ([4080000000000], [2085000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([4515000000000], [2475000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) (.next ([4080000000000, 0], [3060000000000, 9000000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) (.next ([3963000000000], [3492000000000]) (some (6, 1, 4)) (some (6, 1, 4))
      (.next ([3105000000000, -9000000000000], [3060000000000, 9000000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) fan32Owner5Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded32_6 : ExcludedOn (model32.B 6 ++ [step32.q]) 9000000000000 (model32.caps 6)
    (model32.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 5 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 3 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_5 : ExcludedOn (model33.B 5 ++ [step33.q]) 9000000000000 (model33.caps 5)
    (model33.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000], [117000000000]) (some (5, 0, 3))
      (some (5, 1, 3)) (.next ([3240000000000], [585000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([3492000000000], [798000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([5250000000000], [1617000000000]) (some (5, 1, 3)) (some (6, 1, 3)) (.next ([333000000000],
      [135000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4782000000000], [1950000000000])
      (some (6, 1, 3)) (some (6, 1, 4)) (.next ([4080000000000], [2085000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) (.next ([4080000000000, 0], [3060000000000, 9000000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) (.next ([3963000000000], [3492000000000]) (some (6, 1, 4)) (some (6, 1, 4))
      fan33Owner5Part0)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5940000000000, -9000000000000], [3060000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([3240000000000], [4635000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1305000000000, -9000000000000], [7875000000000, 0])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([180000000000, -9000000000000], [4635000000000])
      (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [3060000000000, 9000000000000]) (some (0, 1,
      1)) (some (3, 1, 1)) (.next ([-3060000000000, -9000000000000], [9000000000000, 0]) (some (3,
      1, 1)) (some (3, 1, 2)) (.next ([-4635000000000], [7875000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([-7875000000000, 0], [9180000000000, -9000000000000]) (some (3, 1, 2)) (some
      (3, 1, 2)) (.next ([-4635000000000, 0], [4815000000000, -9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_3 : ExcludedOn (model34.B 3 ++ [step34.q]) 9000000000000 (model34.caps 3)
    (model34.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4635000000000], [1125000000000]) (some (5, 1,
      7)) (some (6, 1, 7)) (.next ([3345000000000], [1290000000000]) (some (6, 1, 7)) (some (6, 1,
      7)) (.next ([3240000000000], [1260000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next
      ([3150000000000], [1350000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([2955000000000],
      [1305000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([2535000000000], [1350000000000])
      (some (6, 1, 5)) (some (6, 1, 5)) (.next ([4455000000000], [2685000000000, 9000000000000])
      (some (6, 1, 5)) (some (6, 1, 5)) (.next ([4470000000000], [3060000000000, 9000000000000])
      (some (6, 1, 5)) (some (6, 1, 5)) (.next ([3150000000000], [3750000000000]) (some (6, 1, 5))
      (some (6, 1, 5)) (.next ([3060000000000], [3750000000000]) (some (6, 1, 5)) (some (6, 1, 5))
      (.next ([3195000000000], [4125000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next
      ([3105000000000], [4125000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([3210000000000],
      [4500000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([3120000000000], [4500000000000])
      (some (6, 1, 5)) (some (6, 1, 5)) (.next ([1575000000000, -9000000000000], [4185000000000,
      9000000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([750000000000], [3660000000000])
      (some (6, 1, 5)) (some (6, 1, 5)) (.next ([45000000000], [375000000000]) (some (6, 1, 5))
      (some (6, 1, 5)) (.next ([375000000000], [4080000000000]) (some (6, 1, 5)) (some (6, 1, 5))
      (.next ([60000000000], [750000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next
      ([15000000000], [375000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([135000000000],
      [4275000000000]) (some (6, 1, 5)) (some (6, 1, 5)) fan34Owner3Part0)))))))))))))))))))))) (den
      :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_4 : ExcludedOn (model34.B 4 ++ [step34.q]) 9000000000000 (model34.caps 4)
    (model34.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7935000000000], [1065000000000]) (some (5, 7,
      7)) (some (6, 7, 7)) (.next ([7545000000000], [1080000000000]) (some (6, 7, 5)) (some (6, 7,
      5)) (.next ([7125000000000], [1125000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next
      ([3240000000000], [1260000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next ([3150000000000],
      [1350000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next ([4410000000000], [2310000000000,
      9000000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next ([4455000000000], [2685000000000,
      9000000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next ([4470000000000], [3060000000000,
      9000000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next ([3150000000000], [3750000000000])
      (some (6, 7, 5)) (some (6, 7, 5)) (.next ([3060000000000], [3750000000000]) (some (6, 7, 5))
      (some (6, 7, 5)) (.next ([3195000000000], [4125000000000]) (some (6, 7, 5)) (some (6, 7, 5))
      (.next ([3105000000000], [4125000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next
      ([3210000000000], [4500000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next ([3120000000000],
      [4500000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next ([3465000000000], [5535000000000])
      (some (6, 7, 5)) (some (6, 7, 5)) (.next ([750000000000], [3660000000000]) (some (6, 7, 5))
      (some (6, 7, 5)) (.next ([45000000000], [375000000000]) (some (6, 7, 5)) (some (6, 7, 5))
      (.next ([375000000000], [4080000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next
      ([60000000000], [750000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next ([315000000000],
      [4185000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next ([405000000000, -9000000000000],
      [5535000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next ([225000000000], [4275000000000])
      (some (6, 7, 5)) (some (6, 7, 5)) (.next ([15000000000], [375000000000]) (some (6, 7, 5))
      (some (6, 7, 5)) fan35Owner3Part0)))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_4 : ExcludedOn (model35.B 4 ++ [step35.q]) 9000000000000 (model35.caps 4)
    (model35.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5850000000000], [270000000000]) (some (7, 0, 4))
      (some (7, 1, 5)) (.next ([1620000000000], [165000000000]) (some (7, 1, 5)) (some (7, 1, 5))
      (.next ([5100000000000], [1020000000000]) (some (7, 1, 5)) (some (7, 1, 5)) (.next
      ([3480000000000], [855000000000]) (some (7, 1, 5)) (some (7, 1, 5)) (.next ([2985000000000],
      [915000000000]) (some (7, 1, 5)) (some (7, 1, 5)) (.next ([1785000000000], [585000000000])
      (some (7, 1, 5)) (some (7, 1, 5)) (.next ([3900000000000], [1350000000000]) (some (7, 1, 5))
      (some (7, 1, 5)) (.next ([2628000000000], [1122000000000]) (some (7, 1, 5)) (some (7, 1, 5))
      (.next ([2460000000000], [1173000000000]) (some (7, 1, 5)) (some (7, 1, 5)) (.next
      ([3633000000000], [1875000000000]) (some (7, 1, 5)) (some (7, 1, 5)) (.next ([1035000000000],
      [585000000000]) (some (7, 1, 5)) (some (7, 1, 5)) (.next ([3480000000000], [2055000000000])
      (some (7, 1, 5)) (some (7, 1, 8)) (.next ([2628000000000], [1872000000000]) (some (7, 1, 8))
      (some (7, 1, 8)) fan35Owner4Part1)))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_5 : ExcludedOn (model35.B 5 ++ [step35.q]) 9000000000000 (model35.caps 5)
    (model35.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000], [117000000000]) (some (6, 0, 3))
      (some (6, 1, 3)) (.next ([3240000000000], [585000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      (.next ([2835000000000], [630000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
      ([333000000000], [135000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4080000000000],
      [2085000000000]) (some (6, 1, 3)) (some (6, 1, 4)) (.next ([5535000000000], [3465000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([4080000000000, 0], [3060000000000, 9000000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3963000000000], [3492000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) (.next ([3105000000000, -9000000000000], [3060000000000, 9000000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) fan35Owner5Part0)))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel)
      0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_6 : ExcludedOn (model35.B 6 ++ [step35.q]) 9000000000000 (model35.caps 6)
    (model35.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded35_1
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

end Sint340000350000
end ConwaySoifer.Simplified.Certificates
