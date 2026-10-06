/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint100000110000
import Mathlib.Tactic.FinCases

/-!
# Sint 100000 110000 3

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
namespace Sint100000110000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner0Part0 : FanWitness := (.next ([588000000000, -2670000000000], [8229000000000,
    5340000000000]) (some (6, 3, 7)) (some (6, 3, 7)) (.next ([321000000000, -5340000000000],
    [7962000000000, 2670000000000]) (some (6, 3, 7)) (some (6, 3, 7)) (.next ([84000000000,
    5340000000000], [5733000000000, -2670000000000]) (some (6, 3, 7)) (some (6, 7, 7)) (.next ([0],
    [750000000000]) (some (6, 7, 7)) (some (6, 7, 7)) (.next ([-183000000000, 2670000000000],
    [6267000000000, 2670000000000]) (some (0, 7, 7)) (some (0, 7, 7)) (.next ([-366000000000,
    5340000000000], [5883000000000, -2670000000000]) (some (0, 7, 7)) (some (0, 7, 7)) (.next
    ([-366000000000, 5340000000000], [5133000000000, -2670000000000]) (some (0, 7, 7)) (some (0, 7,
    7)) (.next ([-633000000000, 2670000000000], [6417000000000, 2670000000000]) (some (0, 7, 7))
    (some (1, 7, 7)) (.next ([-633000000000, 2670000000000], [5667000000000, 2670000000000]) (some
    (1, 7, 7)) (some (1, 7, 7)) (.next ([-984000000000, -5340000000000], [6267000000000,
    2670000000000]) (some (1, 7, 7)) (some (1, 7, 7)) (.next ([-1167000000000, -2670000000000],
    [6684000000000, 5340000000000]) (some (1, 7, 7)) (some (1, 7, 7)) (.next ([-1167000000000,
    -2670000000000], [5934000000000, 5340000000000]) (some (1, 7, 7)) (some (1, 7, 7)) (.next
    ([-1434000000000, -5340000000000], [6417000000000, 2670000000000]) (some (1, 7, 7)) (some (1, 7,
    7)) (.next ([-2145000000000], [9000000000000]) (some (1, 7, 7)) (some (1, 7, 7)) (.next
    ([-1434000000000, -5340000000000], [5667000000000, 2670000000000]) (some (1, 7, 5)) (some (1, 7,
    5)) (.next ([-3195000000000], [9450000000000]) (some (1, 7, 5)) (some (1, 7, 5)) (.next
    ([-267000000000, -2670000000000], [534000000000, 5340000000000]) (some (1, 7, 5)) (some (1, 7,
    5)) (.next ([-600000000000], [1050000000000]) (some (1, 7, 5)) (some (2, 7, 5)) (.next
    ([-300000000000], [450000000000]) (some (2, 7, 5)) (some (2, 7, 5)) (.next ([-7962000000000,
    -2670000000000], [9084000000000, 5340000000000]) (some (2, 7, 5)) (some (2, 7, 6)) (.next
    ([-7428000000000, 2670000000000], [8016000000000, -5340000000000]) (some (2, 7, 6)) (some (2, 7,
    6)) (.next ([-8229000000000, -5340000000000], [8817000000000, 2670000000000]) (some (2, 7, 6))
    (some (2, 7, 6)) (.next ([-7962000000000, -2670000000000], [8283000000000, -2670000000000])
    (some (2, 7, 6)) (some (2, 7, 6)) (.next ([-5733000000000, 2670000000000], [5817000000000,
    2670000000000]) (some (2, 7, 6)) (some (2, 7, 6)) (.terminal (some (2, 7, 6)) (some (2, 7, 6))
    (some (2, 7, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner6Part0 : FanWitness := (.next ([1350000000000], [900000000000]) (some (6, 1, 6)) (some
    (6, 2, 6)) (.next ([900000000000, 9000000000000], [900000000000, 9000000000000]) (some (6, 2,
    6)) (some (6, 2, 6)) (.next ([750000000000], [1350000000000]) (some (6, 2, 6)) (some (6, 2, 6))
    (.next ([750000000000, -9000000000000], [1500000000000, 9000000000000]) (some (6, 2, 6)) (some
    (6, 2, 6)) (.next ([1800000000000], [6495000000000]) (some (6, 2, 6)) (some (6, 2, 6)) (.next
    ([1800000000000], [6795000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([1650000000000],
    [7395000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([450000000000, 9000000000000],
    [8145000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([0], [300000000000]) (some (5, 2, 6))
    (some (5, 2, 6)) (.next ([-450000000000], [8145000000000]) (some (0, 2, 6)) (some (0, 3, 6))
    (.next ([-450000000000], [7245000000000, -9000000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([-150000000000, -9000000000000], [2250000000000, 9000000000000]) (some (0, 3, 6)) (some
    (0, 3, 6)) (.next ([-150000000000], [900000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-150000000000], [600000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-600000000000],
    [2250000000000]) (some (0, 3, 6)) (some (1, 3, 6)) (.next ([-450000000000, 9000000000000],
    [1200000000000, -9000000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-900000000000],
    [2250000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-900000000000, -9000000000000],
    [1800000000000, 18000000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-1350000000000],
    [2100000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-1500000000000, -9000000000000],
    [2250000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-6495000000000], [8295000000000])
    (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-6795000000000], [8595000000000]) (some (1, 3, 6))
    (some (1, 3, 6)) (.next ([-7395000000000], [9045000000000]) (some (1, 3, 6)) (some (1, 3, 6))
    (.next ([-8145000000000, 0], [8595000000000, 9000000000000]) (some (1, 3, 6)) (some (1, 3, 6))
    (.terminal (some (1, 3, 6)) (some (1, 3, 6)) (some (1, 3, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner6Part0 : FanWitness := (.next ([1650000000000], [600000000000]) (some (5, 6, 4)) (some
    (5, 6, 4)) (.next ([750000000000, 0], [450000000000, -9000000000000]) (some (5, 6, 4)) (some (5,
    6, 4)) (.next ([1350000000000], [900000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
    ([900000000000, 9000000000000], [900000000000, 9000000000000]) (some (5, 6, 4)) (some (5, 6, 4))
    (.next ([750000000000], [1350000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
    ([750000000000, -9000000000000], [1500000000000, 9000000000000]) (some (5, 6, 4)) (some (5, 6,
    4)) (.next ([300000000000, 9000000000000], [1350000000000, -9000000000000]) (some (5, 6, 4))
    (some (5, 6, 4)) (.next ([0, 9000000000000], [1350000000000, -9000000000000]) (some (5, 6, 4))
    (some (5, 6, 4)) (.next ([0], [300000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
    ([-150000000000, -9000000000000], [2250000000000, 9000000000000]) (some (0, 6, 4)) (some (0, 6,
    4)) (.next ([-900000000000, -9000000000000], [7380000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-150000000000], [900000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-2250000000000], [9030000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-150000000000],
    [600000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2250000000000], [8730000000000])
    (some (0, 6, 4)) (some (1, 6, 4)) (.next ([-2100000000000], [8130000000000]) (some (1, 6, 4))
    (some (1, 6, 4)) (.next ([-600000000000], [2250000000000]) (some (1, 6, 4)) (some (6, 6, 4))
    (.next ([-450000000000, 9000000000000], [1200000000000, -9000000000000]) (some (6, 6, 4)) (some
    (6, 6, 4)) (.next ([-900000000000], [2250000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next
    ([-900000000000, -9000000000000], [1800000000000, 18000000000000]) (some (6, 6, 4)) (some (6, 6,
    4)) (.next ([-1350000000000], [2100000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next
    ([-1500000000000, -9000000000000], [2250000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next
    ([-1350000000000, 9000000000000], [1650000000000]) (some (6, 6, 4)) (some (6, 6, 5)) (.next
    ([-1350000000000, 9000000000000], [1350000000000]) (some (6, 6, 5)) (some (6, 6, 5)) (.terminal
    (some (6, 6, 5)) (some (6, 3, 5)) (some (6, 6, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan26Owner0Part0 : FanWitness := (.next ([591000000000, -5340000000000], [8142000000000,
    2670000000000]) (some (6, 3, 7)) (some (6, 3, 7)) (.next ([84000000000, 5340000000000],
    [5733000000000, -2670000000000]) (some (6, 3, 7)) (some (6, 7, 7)) (.next ([0], [750000000000])
    (some (6, 7, 7)) (some (6, 7, 7)) (.next ([-183000000000, 2670000000000], [6267000000000,
    2670000000000]) (some (0, 7, 7)) (some (0, 7, 7)) (.next ([-366000000000, 5340000000000],
    [5883000000000, -2670000000000]) (some (0, 7, 7)) (some (0, 7, 7)) (.next ([-366000000000,
    5340000000000], [5133000000000, -2670000000000]) (some (0, 7, 7)) (some (0, 7, 7)) (.next
    ([-633000000000, 2670000000000], [6417000000000, 2670000000000]) (some (0, 7, 7)) (some (1, 7,
    7)) (.next ([-633000000000, 2670000000000], [5667000000000, 2670000000000]) (some (1, 7, 7))
    (some (1, 7, 7)) (.next ([-984000000000, -5340000000000], [6267000000000, 2670000000000]) (some
    (1, 7, 7)) (some (1, 7, 7)) (.next ([-1167000000000, -2670000000000], [6684000000000,
    5340000000000]) (some (1, 7, 7)) (some (1, 7, 7)) (.next ([-1167000000000, -2670000000000],
    [5934000000000, 5340000000000]) (some (1, 7, 7)) (some (1, 7, 7)) (.next ([-1434000000000,
    -5340000000000], [6417000000000, 2670000000000]) (some (1, 7, 7)) (some (1, 7, 7)) (.next
    ([-2325000000000], [9450000000000]) (some (1, 7, 7)) (some (1, 7, 7)) (.next ([-1434000000000,
    -5340000000000], [5667000000000, 2670000000000]) (some (1, 7, 5)) (some (1, 7, 5)) (.next
    ([-2625000000000], [9900000000000]) (some (1, 7, 5)) (some (1, 7, 5)) (.next ([-3375000000000],
    [9900000000000]) (some (1, 7, 5)) (some (1, 7, 5)) (.next ([-267000000000, -2670000000000],
    [534000000000, 5340000000000]) (some (1, 7, 5)) (some (1, 7, 5)) (.next ([-600000000000],
    [1050000000000]) (some (1, 7, 5)) (some (2, 7, 5)) (.next ([-300000000000], [450000000000])
    (some (2, 7, 5)) (some (2, 7, 5)) (.next ([-8142000000000, -2670000000000], [9534000000000,
    5340000000000]) (some (2, 7, 5)) (some (2, 7, 6)) (.next ([-7608000000000, 2670000000000],
    [8466000000000, -5340000000000]) (some (2, 7, 6)) (some (2, 7, 6)) (.next ([-8409000000000,
    -5340000000000], [9267000000000, 2670000000000]) (some (2, 7, 6)) (some (2, 7, 6)) (.next
    ([-8142000000000, -2670000000000], [8733000000000, -2670000000000]) (some (2, 7, 6)) (some (2,
    7, 6)) (.next ([-5733000000000, 2670000000000], [5817000000000, 2670000000000]) (some (2, 7, 6))
    (some (2, 7, 6)) (.terminal (some (2, 7, 6)) (some (2, 7, 6)) (some (2, 7,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan26Owner6Part0 : FanWitness := (.next ([750000000000], [1350000000000]) (some (6, 2, 6)) (some
    (6, 2, 6)) (.next ([750000000000, -9000000000000], [1500000000000, 9000000000000]) (some (6, 2,
    6)) (some (6, 2, 6)) (.next ([2250000000000], [6225000000000]) (some (6, 2, 6)) (some (6, 2, 6))
    (.next ([2250000000000], [6525000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next
    ([2100000000000], [7125000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([450000000000,
    -9000000000000], [1800000000000, 9000000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next
    ([900000000000, 9000000000000], [7875000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([0,
    9000000000000], [1350000000000, -9000000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([0],
    [300000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([-150000000000, -9000000000000],
    [2250000000000, 9000000000000]) (some (0, 2, 6)) (some (0, 3, 6)) (.next ([-150000000000],
    [900000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-150000000000], [600000000000]) (some
    (0, 3, 6)) (some (0, 3, 6)) (.next ([-600000000000], [2250000000000]) (some (0, 3, 6)) (some (1,
    3, 6)) (.next ([-450000000000, 9000000000000], [1200000000000, -9000000000000]) (some (1, 3, 6))
    (some (1, 3, 6)) (.next ([-900000000000], [2250000000000]) (some (1, 3, 6)) (some (1, 3, 6))
    (.next ([-900000000000, -9000000000000], [1800000000000, 18000000000000]) (some (1, 3, 6)) (some
    (1, 3, 6)) (.next ([-1350000000000], [2100000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next
    ([-1500000000000, -9000000000000], [2250000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next
    ([-6225000000000], [8475000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-6525000000000],
    [8775000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-7125000000000], [9225000000000])
    (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-1800000000000, -9000000000000], [2250000000000])
    (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-7875000000000, 0], [8775000000000, 9000000000000])
    (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-1350000000000, 9000000000000], [1350000000000])
    (some (1, 3, 6)) (some (1, 3, 6)) (.terminal (some (1, 3, 6)) (some (1, 3, 6)) (some (1, 3,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner1Part0 : FanWitness := (.next ([1305000000000, 0], [450000000000, 9000000000000])
    (some (5, 5, 4)) (some (5, 5, 4)) (.next ([525000000000], [225000000000]) (some (5, 5, 4)) (some
    (5, 5, 4)) (.next ([5880000000000], [3570000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next
    ([6150000000000], [3750000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([5625000000000],
    [3525000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([270000000000], [180000000000]) (some
    (5, 2, 4)) (some (5, 2, 4)) (.next ([750000000000], [600000000000]) (some (5, 2, 4)) (some (5,
    3, 4)) (.next ([1125000000000, 0], [900000000000, 9000000000000]) (some (5, 3, 4)) (some (5, 3,
    4)) (.next ([5025000000000], [4875000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next
    ([4125000000000, -9000000000000], [4875000000000, 0]) (some (5, 3, 4)) (some (5, 3, 4)) (.next
    ([450000000000], [855000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([0, 0],
    [900000000000, 9000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-150000000000,
    -9000000000000], [1500000000000, 9000000000000]) (some (5, 3, 0)) (some (5, 3, 0)) (.next
    ([-450000000000, -9000000000000], [1755000000000, 9000000000000]) (some (5, 3, 0)) (some (5, 3,
    0)) (.next ([-225000000000], [750000000000]) (some (5, 3, 0)) (some (5, 3, 0)) (.next
    ([-3570000000000], [9450000000000]) (some (5, 3, 0)) (some (5, 3, 0)) (.next ([-3750000000000],
    [9900000000000]) (some (5, 3, 0)) (some (5, 3, 0)) (.next ([-3525000000000], [9150000000000])
    (some (5, 3, 0)) (some (5, 3, 0)) (.next ([-180000000000], [450000000000]) (some (5, 3, 0))
    (some (5, 3, 0)) (.next ([-600000000000], [1350000000000]) (some (5, 3, 0)) (some (5, 3, 0))
    (.next ([-900000000000, -9000000000000], [2025000000000, 9000000000000]) (some (5, 3, 0)) (some
    (5, 3, 0)) (.next ([-4875000000000], [9900000000000]) (some (5, 3, 0)) (some (5, 3, 0)) (.next
    ([-4875000000000, 0], [9000000000000, -9000000000000]) (some (5, 3, 0)) (some (5, 3, 0)) (.next
    ([-855000000000], [1305000000000]) (some (5, 3, 0)) (some (5, 3, 5)) (.terminal (some (5, 3, 5))
    (some (5, 3, 5)) (some (5, 3, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan29Owner1Part0 : FanWitness := (.next ([7380000000000], [2070000000000]) (some (5, 5, 4))
    (some (5, 5, 4)) (.next ([7125000000000], [2025000000000]) (some (5, 2, 4)) (some (5, 2, 4))
    (.next ([7650000000000], [2250000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
    ([1305000000000, 0], [450000000000, 9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
    ([525000000000], [225000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([6525000000000],
    [3375000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([5625000000000, -9000000000000],
    [3375000000000, 0]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([270000000000], [180000000000])
    (some (5, 2, 4)) (some (5, 2, 4)) (.next ([750000000000], [600000000000]) (some (5, 2, 4)) (some
    (5, 3, 4)) (.next ([1125000000000, 0], [900000000000, 9000000000000]) (some (5, 3, 4)) (some (5,
    3, 4)) (.next ([450000000000], [855000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([0, 0],
    [900000000000, 9000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-150000000000,
    -9000000000000], [1500000000000, 9000000000000]) (some (5, 3, 0)) (some (5, 3, 0)) (.next
    ([-2070000000000], [9450000000000]) (some (5, 3, 0)) (some (5, 3, 0)) (.next ([-2025000000000],
    [9150000000000]) (some (5, 3, 0)) (some (5, 3, 0)) (.next ([-2250000000000], [9900000000000])
    (some (5, 3, 0)) (some (5, 3, 0)) (.next ([-450000000000, -9000000000000], [1755000000000,
    9000000000000]) (some (5, 3, 0)) (some (5, 3, 0)) (.next ([-225000000000], [750000000000]) (some
    (5, 3, 0)) (some (5, 3, 0)) (.next ([-3375000000000], [9900000000000]) (some (5, 3, 0)) (some
    (5, 3, 0)) (.next ([-3375000000000, 0], [9000000000000, -9000000000000]) (some (5, 3, 0)) (some
    (5, 3, 0)) (.next ([-180000000000], [450000000000]) (some (5, 3, 0)) (some (5, 3, 5)) (.next
    ([-600000000000], [1350000000000]) (some (5, 3, 5)) (some (5, 3, 5)) (.next ([-900000000000,
    -9000000000000], [2025000000000, 9000000000000]) (some (5, 3, 5)) (some (5, 3, 5)) (.next
    ([-855000000000], [1305000000000]) (some (5, 3, 5)) (some (5, 3, 5)) (.terminal (some (5, 3, 5))
    (some (5, 3, 5)) (some (5, 3, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan30Owner1Part0 : FanWitness := (.next ([7860000000000], [315000000000]) none none (.next
    ([8130000000000], [495000000000]) none none (.next ([1350000000000, 0], [150000000000,
    9000000000000]) none none (.next ([7005000000000], [1620000000000]) none none (.next
    ([6105000000000, -9000000000000], [1620000000000, 0]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
    ([1305000000000, 0], [450000000000, 9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
    ([525000000000], [225000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([270000000000],
    [180000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([750000000000], [600000000000]) (some
    (5, 2, 4)) (some (5, 3, 4)) (.next ([1125000000000, 0], [900000000000, 9000000000000]) (some (5,
    3, 4)) (some (5, 3, 4)) (.next ([450000000000], [855000000000]) (some (5, 3, 4)) (some (5, 3,
    4)) (.next ([0, 0], [900000000000, 9000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next
    ([-270000000000], [7875000000000]) (some (5, 3, 0)) (some (5, 3, 0)) (.next ([-315000000000],
    [8175000000000]) (some (5, 3, 0)) (some (5, 3, 0)) (.next ([-495000000000], [8625000000000])
    (some (5, 3, 0)) (some (5, 3, 0)) (.next ([-150000000000, -9000000000000], [1500000000000,
    9000000000000]) (some (5, 3, 0)) (some (5, 3, 0)) (.next ([-1620000000000], [8625000000000])
    (some (5, 3, 0)) (some (5, 3, 0)) (.next ([-1620000000000, 0], [7725000000000, -9000000000000])
    (some (5, 3, 0)) (some (5, 3, 0)) (.next ([-450000000000, -9000000000000], [1755000000000,
    9000000000000]) (some (5, 3, 0)) (some (5, 3, 5)) (.next ([-225000000000], [750000000000]) (some
    (5, 3, 5)) (some (5, 3, 5)) (.next ([-180000000000], [450000000000]) (some (5, 3, 5)) (some (5,
    3, 5)) (.next ([-600000000000], [1350000000000]) (some (5, 3, 5)) (some (5, 3, 5)) (.next
    ([-900000000000, -9000000000000], [2025000000000, 9000000000000]) (some (5, 3, 5)) (some (5, 3,
    5)) (.next ([-855000000000], [1305000000000]) (some (5, 3, 5)) (some (5, 3, 5)) (.terminal (some
    (5, 3, 5)) none none)))))))))))))))))))))))))

theorem excluded24_0 : ExcludedOn (model24.B 0 ++ [step24.q]) 9000000000000 (model24.caps 0)
    (model24.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6084000000000, 5340000000000], [183000000000,
      -2670000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([5517000000000, 2670000000000],
      [366000000000, -5340000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([4767000000000,
      2670000000000], [366000000000, -5340000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([5784000000000, 5340000000000], [633000000000, -2670000000000]) (some (6, 2, 7)) (some (6, 2,
      7)) (.next ([5034000000000, 5340000000000], [633000000000, -2670000000000]) (some (6, 2, 7))
      (some (6, 2, 7)) (.next ([5283000000000, -2670000000000], [984000000000, 5340000000000]) (some
      (6, 2, 7)) (some (6, 2, 7)) (.next ([5517000000000, 2670000000000], [1167000000000,
      2670000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([4767000000000, 2670000000000],
      [1167000000000, 2670000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([4983000000000,
      -2670000000000], [1434000000000, 5340000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([6855000000000], [2145000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([4233000000000,
      -2670000000000], [1434000000000, 5340000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([6255000000000], [3195000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([267000000000,
      2670000000000], [267000000000, 2670000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([450000000000], [600000000000]) (some (6, 2, 7)) (some (6, 3, 7)) (.next ([150000000000],
      [300000000000]) (some (6, 3, 7)) (some (6, 3, 7)) (.next ([1122000000000, 2670000000000],
      [7962000000000, 2670000000000]) (some (6, 3, 7)) (some (6, 3, 7)) (.next ([588000000000,
      -2670000000000], [7428000000000, -2670000000000]) (some (6, 3, 7)) (some (6, 3, 7))
      fan24Owner0Part0)))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_2 : ExcludedOn (model24.B 2 ++ [step24.q]) 9000000000000 (model24.caps 2)
    (model24.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_3 : ExcludedOn (model24.B 3 ++ [step24.q]) 9000000000000 (model24.caps 3)
    (model24.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_4 : ExcludedOn (model24.B 4 ++ [step24.q]) 9000000000000 (model24.caps 4)
    (model24.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_5 : ExcludedOn (model24.B 5 ++ [step24.q]) 9000000000000 (model24.caps 5)
    (model24.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_6 : ExcludedOn (model24.B 6 ++ [step24.q]) 9000000000000 (model24.caps 6)
    (model24.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7695000000000], [450000000000]) (some (6, 1, 3))
      (some (6, 1, 4)) (.next ([6795000000000, -9000000000000], [450000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) (.next ([2100000000000], [150000000000, 9000000000000]) (some (6, 1, 4))
      (some (6, 1, 6)) (.next ([750000000000], [150000000000]) (some (6, 1, 6)) (some (6, 1, 6))
      (.next ([450000000000], [150000000000]) (some (6, 1, 6)) (some (6, 1, 6)) (.next
      ([1650000000000], [600000000000]) (some (6, 1, 6)) (some (6, 1, 6)) (.next ([750000000000, 0],
      [450000000000, -9000000000000]) (some (6, 1, 6)) (some (6, 1, 6)) fan24Owner6Part0))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_7 : ExcludedOn (model24.B 7 ++ [step24.q]) 9000000000000 (model24.caps 7)
    (model24.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_8 : ExcludedOn (model24.B 8 ++ [step24.q]) 9000000000000 (model24.caps 8)
    (model24.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_9 : ExcludedOn (model24.B 9 ++ [step24.q]) 9000000000000 (model24.caps 9)
    (model24.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked24 : StepValid model24 9000000000000 step24 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded24_0
    · exact (hj rfl).elim
    · exact excluded24_2
    · exact excluded24_3
    · exact excluded24_4
    · exact excluded24_5
    · exact excluded24_6
    · exact excluded24_7
    · exact excluded24_8
    · exact excluded24_9
theorem next24 : model24.insert step24 = model25 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded25_0 : ExcludedOn (model25.B 0 ++ [step25.q]) 9000000000000 (model25.caps 0)
    (model25.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_1 : ExcludedOn (model25.B 1 ++ [step25.q]) 9000000000000 (model25.caps 1)
    (model25.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_2 : ExcludedOn (model25.B 2 ++ [step25.q]) 9000000000000 (model25.caps 2)
    (model25.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_3 : ExcludedOn (model25.B 3 ++ [step25.q]) 9000000000000 (model25.caps 3)
    (model25.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_4 : ExcludedOn (model25.B 4 ++ [step25.q]) 9000000000000 (model25.caps 4)
    (model25.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_5 : ExcludedOn (model25.B 5 ++ [step25.q]) 9000000000000 (model25.caps 5)
    (model25.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_6 : ExcludedOn (model25.B 6 ++ [step25.q]) 9000000000000 (model25.caps 6)
    (model25.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2100000000000], [150000000000, 9000000000000])
      (some (5, 6, 3)) (some (5, 6, 4)) (.next ([6480000000000, -9000000000000], [900000000000,
      9000000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([750000000000], [150000000000])
      (some (5, 6, 4)) (some (5, 6, 4)) (.next ([6780000000000], [2250000000000]) (some (5, 6, 4))
      (some (5, 6, 4)) (.next ([450000000000], [150000000000]) (some (5, 6, 4)) (some (5, 6, 4))
      (.next ([6480000000000], [2250000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
      ([6030000000000], [2100000000000]) (some (5, 6, 4)) (some (5, 6, 4)) fan25Owner6Part0))))))))
      (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_7 : ExcludedOn (model25.B 7 ++ [step25.q]) 9000000000000 (model25.caps 7)
    (model25.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_8 : ExcludedOn (model25.B 8 ++ [step25.q]) 9000000000000 (model25.caps 8)
    (model25.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked25 : StepValid model25 9000000000000 step25 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded25_0
    · exact excluded25_1
    · exact excluded25_2
    · exact excluded25_3
    · exact excluded25_4
    · exact excluded25_5
    · exact excluded25_6
    · exact excluded25_7
    · exact excluded25_8
    · exact (hj rfl).elim
theorem next25 : model25.insert step25 = model26 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded26_0 : ExcludedOn (model26.B 0 ++ [step26.q]) 9000000000000 (model26.caps 0)
    (model26.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6084000000000, 5340000000000], [183000000000,
      -2670000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([5517000000000, 2670000000000],
      [366000000000, -5340000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([4767000000000,
      2670000000000], [366000000000, -5340000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([5784000000000, 5340000000000], [633000000000, -2670000000000]) (some (6, 2, 7)) (some (6, 2,
      7)) (.next ([5034000000000, 5340000000000], [633000000000, -2670000000000]) (some (6, 2, 7))
      (some (6, 2, 7)) (.next ([5283000000000, -2670000000000], [984000000000, 5340000000000]) (some
      (6, 2, 7)) (some (6, 2, 7)) (.next ([5517000000000, 2670000000000], [1167000000000,
      2670000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([4767000000000, 2670000000000],
      [1167000000000, 2670000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([4983000000000,
      -2670000000000], [1434000000000, 5340000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([7125000000000], [2325000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([4233000000000,
      -2670000000000], [1434000000000, 5340000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([7275000000000], [2625000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([6525000000000],
      [3375000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([267000000000, 2670000000000],
      [267000000000, 2670000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([450000000000],
      [600000000000]) (some (6, 2, 7)) (some (6, 3, 7)) (.next ([150000000000], [300000000000])
      (some (6, 3, 7)) (some (6, 3, 7)) (.next ([1392000000000, 2670000000000], [8142000000000,
      2670000000000]) (some (6, 3, 7)) (some (6, 3, 7)) (.next ([858000000000, -2670000000000],
      [7608000000000, -2670000000000]) (some (6, 3, 7)) (some (6, 3, 7)) (.next ([858000000000,
      -2670000000000], [8409000000000, 5340000000000]) (some (6, 3, 7)) (some (6, 3, 7))
      fan26Owner0Part0)))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded26_2 : ExcludedOn (model26.B 2 ++ [step26.q]) 9000000000000 (model26.caps 2)
    (model26.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_3 : ExcludedOn (model26.B 3 ++ [step26.q]) 9000000000000 (model26.caps 3)
    (model26.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_4 : ExcludedOn (model26.B 4 ++ [step26.q]) 9000000000000 (model26.caps 4)
    (model26.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_5 : ExcludedOn (model26.B 5 ++ [step26.q]) 9000000000000 (model26.caps 5)
    (model26.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_6 : ExcludedOn (model26.B 6 ++ [step26.q]) 9000000000000 (model26.caps 6)
    (model26.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2100000000000], [150000000000, 9000000000000])
      (some (6, 1, 3)) (some (6, 1, 6)) (.next ([750000000000], [150000000000]) (some (6, 1, 6))
      (some (6, 1, 6)) (.next ([450000000000], [150000000000]) (some (6, 1, 6)) (some (6, 1, 6))
      (.next ([1650000000000], [600000000000]) (some (6, 1, 6)) (some (6, 1, 6)) (.next
      ([750000000000, 0], [450000000000, -9000000000000]) (some (6, 1, 6)) (some (6, 1, 6)) (.next
      ([1350000000000], [900000000000]) (some (6, 1, 6)) (some (6, 2, 6)) (.next ([900000000000,
      9000000000000], [900000000000, 9000000000000]) (some (6, 2, 6)) (some (6, 2, 6))
      fan26Owner6Part0)))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded26_7 : ExcludedOn (model26.B 7 ++ [step26.q]) 9000000000000 (model26.caps 7)
    (model26.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_8 : ExcludedOn (model26.B 8 ++ [step26.q]) 9000000000000 (model26.caps 8)
    (model26.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_9 : ExcludedOn (model26.B 9 ++ [step26.q]) 9000000000000 (model26.caps 9)
    (model26.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked26 : StepValid model26 9000000000000 step26 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded26_0
    · exact (hj rfl).elim
    · exact excluded26_2
    · exact excluded26_3
    · exact excluded26_4
    · exact excluded26_5
    · exact excluded26_6
    · exact excluded26_7
    · exact excluded26_8
    · exact excluded26_9
theorem next26 : model26.insert step26 = model27 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded27_0 : ExcludedOn (model27.B 0 ++ [step27.q]) 9000000000000 (model27.caps 0)
    (model27.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_1 : ExcludedOn (model27.B 1 ++ [step27.q]) 9000000000000 (model27.caps 1)
    (model27.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_2 : ExcludedOn (model27.B 2 ++ [step27.q]) 9000000000000 (model27.caps 2)
    (model27.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_3 : ExcludedOn (model27.B 3 ++ [step27.q]) 9000000000000 (model27.caps 3)
    (model27.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_5 : ExcludedOn (model27.B 5 ++ [step27.q]) 9000000000000 (model27.caps 5)
    (model27.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6150000000000, 0], [900000000000,
      9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([4500000000000], [900000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3600000000000, -9000000000000], [1800000000000,
      9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2700000000000], [1500000000000])
      (some (4, 1, 2)) (some (4, 1, 3)) (.next ([3000000000000], [5100000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([1050000000000], [1950000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([2100000000000, -9000000000000], [6000000000000, 9000000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([750000000000], [4500000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([0], [6150000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-900000000000,
      -9000000000000], [7050000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next
      ([-900000000000], [5400000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1800000000000,
      -9000000000000], [5400000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1500000000000],
      [4200000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-5100000000000], [8100000000000])
      (some (0, 2, 3)) (some (0, 2, 4)) (.next ([-1950000000000], [3000000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-6000000000000, -9000000000000], [8100000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-4500000000000], [5250000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_6 : ExcludedOn (model27.B 6 ++ [step27.q]) 9000000000000 (model27.caps 6)
    (model27.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_7 : ExcludedOn (model27.B 7 ++ [step27.q]) 9000000000000 (model27.caps 7)
    (model27.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_8 : ExcludedOn (model27.B 8 ++ [step27.q]) 9000000000000 (model27.caps 8)
    (model27.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_9 : ExcludedOn (model27.B 9 ++ [step27.q]) 9000000000000 (model27.caps 9)
    (model27.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked27 : StepValid model27 9000000000000 step27 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded27_0
    · exact excluded27_1
    · exact excluded27_2
    · exact excluded27_3
    · exact (hj rfl).elim
    · exact excluded27_5
    · exact excluded27_6
    · exact excluded27_7
    · exact excluded27_8
    · exact excluded27_9
theorem next27 : model27.insert step27 = model28 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded28_1 : ExcludedOn (model28.B 1 ++ [step28.q]) 9000000000000 (model28.caps 1)
    (model28.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1350000000000, 0], [150000000000,
      9000000000000]) (some (5, 5, 3)) (some (5, 5, 4)) fan28Owner1Part0)) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded28_2 : ExcludedOn (model28.B 2 ++ [step28.q]) 9000000000000 (model28.caps 2)
    (model28.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3975000000000, -9000000000000], [0,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([8100000000000, -9000000000000],
      [900000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4125000000000,
      -9000000000000], [4875000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([900000000000],
      [3975000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [900000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, -9000000000000],
      [3975000000000]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-900000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (3, 1, 2)) (.next ([-4875000000000, 0],
      [9000000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3975000000000],
      [4875000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_3 : ExcludedOn (model28.B 3 ++ [step28.q]) 9000000000000 (model28.caps 3)
    (model28.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7245000000000], [900000000000, 9000000000000])
      (some (2, 0, 4)) (some (3, 0, 4)) (.next ([6945000000000], [1200000000000]) (some (3, 0, 4))
      (some (3, 1, 4)) (.next ([3120000000000], [855000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([900000000000], [300000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([3975000000000], [4125000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([3075000000000,
      -9000000000000], [5025000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([2775000000000], [5025000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [900000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 4, 2)) (.next ([-900000000000,
      -9000000000000], [8145000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1200000000000], [8145000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-855000000000],
      [3975000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-300000000000], [1200000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4125000000000], [8100000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-5025000000000, -9000000000000], [8100000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-5025000000000], [7800000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded28_4 : ExcludedOn (model28.B 4 ++ [step28.q]) 9000000000000 (model28.caps 4)
    (model28.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_5 : ExcludedOn (model28.B 5 ++ [step28.q]) 9000000000000 (model28.caps 5)
    (model28.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_6 : ExcludedOn (model28.B 6 ++ [step28.q]) 9000000000000 (model28.caps 6)
    (model28.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_7 : ExcludedOn (model28.B 7 ++ [step28.q]) 9000000000000 (model28.caps 7)
    (model28.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_8 : ExcludedOn (model28.B 8 ++ [step28.q]) 9000000000000 (model28.caps 8)
    (model28.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_9 : ExcludedOn (model28.B 9 ++ [step28.q]) 9000000000000 (model28.caps 9)
    (model28.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked28 : StepValid model28 9000000000000 step28 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded28_1
    · exact excluded28_2
    · exact excluded28_3
    · exact excluded28_4
    · exact excluded28_5
    · exact excluded28_6
    · exact excluded28_7
    · exact excluded28_8
    · exact excluded28_9
theorem next28 : model28.insert step28 = model29 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded29_1 : ExcludedOn (model29.B 1 ++ [step29.q]) 9000000000000 (model29.caps 1)
    (model29.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1350000000000, 0], [150000000000,
      9000000000000]) (some (5, 5, 3)) (some (5, 5, 4)) fan29Owner1Part0)) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded29_2 : ExcludedOn (model29.B 2 ++ [step29.q]) 9000000000000 (model29.caps 2)
    (model29.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2475000000000, -9000000000000], [0,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([8100000000000, -9000000000000],
      [900000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([5625000000000,
      -9000000000000], [3375000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([900000000000],
      [2475000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [900000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, -9000000000000],
      [2475000000000]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-900000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (3, 1, 2)) (.next ([-3375000000000, 0],
      [9000000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2475000000000],
      [3375000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_3 : ExcludedOn (model29.B 3 ++ [step29.q]) 9000000000000 (model29.caps 3)
    (model29.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7245000000000], [900000000000, 9000000000000])
      (some (2, 0, 4)) (some (3, 0, 4)) (.next ([6945000000000], [1200000000000]) (some (3, 0, 4))
      (some (3, 0, 4)) (.next ([900000000000], [300000000000]) (some (3, 0, 4)) (some (3, 1, 4))
      (.next ([1620000000000], [855000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([2475000000000], [5625000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1575000000000,
      -9000000000000], [6525000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([1275000000000], [6525000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [900000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 4, 2)) (.next ([-900000000000,
      -9000000000000], [8145000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1200000000000], [8145000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-300000000000],
      [1200000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-855000000000], [2475000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-5625000000000], [8100000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-6525000000000, -9000000000000], [8100000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-6525000000000], [7800000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded29_4 : ExcludedOn (model29.B 4 ++ [step29.q]) 9000000000000 (model29.caps 4)
    (model29.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_5 : ExcludedOn (model29.B 5 ++ [step29.q]) 9000000000000 (model29.caps 5)
    (model29.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_6 : ExcludedOn (model29.B 6 ++ [step29.q]) 9000000000000 (model29.caps 6)
    (model29.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_7 : ExcludedOn (model29.B 7 ++ [step29.q]) 9000000000000 (model29.caps 7)
    (model29.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_8 : ExcludedOn (model29.B 8 ++ [step29.q]) 9000000000000 (model29.caps 8)
    (model29.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_9 : ExcludedOn (model29.B 9 ++ [step29.q]) 9000000000000 (model29.caps 9)
    (model29.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked29 : StepValid model29 9000000000000 step29 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded29_1
    · exact excluded29_2
    · exact excluded29_3
    · exact excluded29_4
    · exact excluded29_5
    · exact excluded29_6
    · exact excluded29_7
    · exact excluded29_8
    · exact excluded29_9
theorem next29 : model29.insert step29 = model30 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded30_1 : ExcludedOn (model30.B 1 ++ [step30.q]) 9000000000000 (model30.caps 1)
    (model30.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7605000000000], [270000000000]) none none
      fan30Owner1Part0)) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded30_2 : ExcludedOn (model30.B 2 ++ [step30.q]) 9000000000000 (model30.caps 2)
    (model30.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8100000000000, -9000000000000], [900000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1620000000000], [375000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([6105000000000, -9000000000000], [1620000000000, 0])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([720000000000, -9000000000000], [1275000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [900000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-900000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-375000000000],
      [1995000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1620000000000, 0],
      [7725000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1275000000000,
      -9000000000000], [1995000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded30_3 : ExcludedOn (model30.B 3 ++ [step30.q]) 9000000000000 (model30.caps 3)
    (model30.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1995000000000], [135000000000]) (some (2, 0, 4))
      (some (3, 0, 4)) (.next ([7245000000000], [900000000000, 9000000000000]) (some (3, 0, 4))
      (some (3, 0, 4)) (.next ([6945000000000], [1200000000000]) (some (3, 0, 4)) (some (3, 0, 4))
      (.next ([900000000000], [300000000000]) (some (3, 0, 4)) (some (3, 1, 4)) (.next
      ([1995000000000], [7380000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([1095000000000,
      -9000000000000], [8280000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([795000000000], [8280000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0],
      [900000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 4, 4)) (.next ([-135000000000],
      [2130000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.next ([-900000000000, -9000000000000],
      [8145000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1200000000000],
      [8145000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-300000000000], [1200000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-7380000000000], [9375000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-8280000000000, -9000000000000], [9375000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-8280000000000], [9075000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded30_4 : ExcludedOn (model30.B 4 ++ [step30.q]) 9000000000000 (model30.caps 4)
    (model30.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_5 : ExcludedOn (model30.B 5 ++ [step30.q]) 9000000000000 (model30.caps 5)
    (model30.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_6 : ExcludedOn (model30.B 6 ++ [step30.q]) 9000000000000 (model30.caps 6)
    (model30.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_7 : ExcludedOn (model30.B 7 ++ [step30.q]) 9000000000000 (model30.caps 7)
    (model30.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_8 : ExcludedOn (model30.B 8 ++ [step30.q]) 9000000000000 (model30.caps 8)
    (model30.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_9 : ExcludedOn (model30.B 9 ++ [step30.q]) 9000000000000 (model30.caps 9)
    (model30.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked30 : StepValid model30 9000000000000 step30 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded30_1
    · exact excluded30_2
    · exact excluded30_3
    · exact excluded30_4
    · exact excluded30_5
    · exact excluded30_6
    · exact excluded30_7
    · exact excluded30_8
    · exact excluded30_9
theorem next30 : model30.insert step30 = model31 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded31_0 : ExcludedOn (model31.B 0 ++ [step31.q]) 9000000000000 (model31.caps 0)
    (model31.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_1 : ExcludedOn (model31.B 1 ++ [step31.q]) 9000000000000 (model31.caps 1)
    (model31.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_2 : ExcludedOn (model31.B 2 ++ [step31.q]) 9000000000000 (model31.caps 2)
    (model31.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_3 : ExcludedOn (model31.B 3 ++ [step31.q]) 9000000000000 (model31.caps 3)
    (model31.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_4 : ExcludedOn (model31.B 4 ++ [step31.q]) 9000000000000 (model31.caps 4)
    (model31.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_5 : ExcludedOn (model31.B 5 ++ [step31.q]) 9000000000000 (model31.caps 5)
    (model31.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6150000000000, 0], [900000000000,
      9000000000000]) (some (0, 0, 4)) (some (0, 1, 4)) (.next ([4500000000000], [900000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([2850000000000], [750000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([1950000000000, -9000000000000], [750000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([3600000000000, -9000000000000], [1800000000000, 9000000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([5400000000000], [3600000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([900000000000], [3750000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([750000000000], [4500000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [6150000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-900000000000, -9000000000000],
      [7050000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-900000000000],
      [5400000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-750000000000], [3600000000000])
      (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-750000000000, 0], [2700000000000, -9000000000000])
      (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1800000000000, -9000000000000], [5400000000000])
      (some (0, 2, 3)) (some (0, 4, 3)) (.next ([-3600000000000], [9000000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-3750000000000], [4650000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-4500000000000], [5250000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some
      (0, 4, 0)) (some (0, 4, 0)) (some (0, 4, 0))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded31_7 : ExcludedOn (model31.B 7 ++ [step31.q]) 9000000000000 (model31.caps 7)
    (model31.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_8 : ExcludedOn (model31.B 8 ++ [step31.q]) 9000000000000 (model31.caps 8)
    (model31.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_9 : ExcludedOn (model31.B 9 ++ [step31.q]) 9000000000000 (model31.caps 9)
    (model31.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3600000000000], [3450000000000]) (some (3, 0,
      1)) (some (3, 1, 2)) (.next ([1080000000000], [1620000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([3600000000000], [6150000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([1980000000000], [6150000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [2700000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-3450000000000], [7050000000000])
      (some (3, 1, 3)) (some (3, 1, 3)) (.next ([-1620000000000], [2700000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-6150000000000], [9750000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-6150000000000], [8130000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some
      (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem checked31 : StepValid model31 9000000000000 step31 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded31_0
    · exact excluded31_1
    · exact excluded31_2
    · exact excluded31_3
    · exact excluded31_4
    · exact excluded31_5
    · exact (hj rfl).elim
    · exact excluded31_7
    · exact excluded31_8
    · exact excluded31_9
theorem next31 : model31.insert step31 = model32 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint100000110000
end ConwaySoifer.Simplified.Certificates
