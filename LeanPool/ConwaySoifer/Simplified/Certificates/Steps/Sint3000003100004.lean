/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint300000310000
import Mathlib.Tactic.FinCases

/-!
# Sint 300000 310000 4

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
namespace Sint300000310000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner0Part0 : FanWitness := (.next ([-375000000000], [3000000000000]) (some (9, 9, 6))
    (some (9, 9, 6)) (.next ([-375000000000], [2850000000000]) (some (9, 4, 6)) (some (9, 4, 6))
    (.next ([-1200000000000], [6000000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([-975000000000], [4200000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-975000000000],
    [2250000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-600000000000], [1350000000000])
    (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-600000000000], [1200000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) (.next ([-750000000000], [1350000000000]) (some (9, 4, 6)) (some (9, 5, 6))
    (.next ([-4200000000000], [6600000000000]) (some (9, 5, 6)) (some (9, 5, 6)) (.next
    ([-4350000000000], [6750000000000]) (some (9, 5, 6)) (some (9, 5, 6)) (.next ([-600000000000],
    [900000000000]) (some (9, 5, 6)) (some (9, 5, 6)) (.next ([-6675000000000], [9600000000000])
    (some (9, 5, 6)) (some (9, 5, 7)) (.next ([-4500000000000], [6000000000000]) (some (9, 5, 7))
    (some (9, 5, 7)) (.next ([-5550000000000], [7350000000000]) (some (9, 5, 7)) (some (9, 5, 7))
    (.next ([-4650000000000], [6150000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next
    ([-6975000000000], [9000000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next ([-5700000000000],
    [7350000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next ([-2325000000000], [2850000000000])
    (some (9, 5, 7)) (some (9, 5, 7)) (.next ([-2475000000000], [3000000000000]) (some (9, 5, 7))
    (some (9, 5, 7)) (.next ([-5850000000000], [6750000000000]) (some (9, 5, 7)) (some (9, 5, 7))
    (.next ([-6000000000000], [6750000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next
    ([-1950000000000], [2100000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next ([-6300000000000],
    [6750000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next ([-6300000000000], [6600000000000])
    (some (9, 5, 7)) (some (9, 5, 7)) (.terminal (some (9, 5, 7)) (some (9, 5, 7)) (some (9, 5,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner0Part1 : FanWitness := (.next ([750000000000], [600000000000]) (some (7, 9, 6)) (some
    (7, 9, 6)) (.next ([600000000000], [600000000000]) (some (7, 9, 6)) (some (7, 9, 6)) (.next
    ([600000000000], [750000000000]) (some (7, 9, 6)) (some (7, 9, 6)) (.next ([2400000000000],
    [4200000000000]) (some (7, 9, 6)) (some (7, 9, 6)) (.next ([2400000000000], [4350000000000])
    (some (7, 9, 6)) (some (7, 9, 6)) (.next ([300000000000], [600000000000]) (some (7, 9, 6)) (some
    (7, 9, 6)) (.next ([2925000000000], [6675000000000]) (some (7, 9, 6)) (some (7, 9, 6)) (.next
    ([1500000000000], [4500000000000]) (some (7, 9, 6)) (some (7, 9, 6)) (.next ([1800000000000],
    [5550000000000]) (some (7, 9, 6)) (some (8, 9, 6)) (.next ([1500000000000], [4650000000000])
    (some (8, 9, 6)) (some (8, 9, 6)) (.next ([2025000000000], [6975000000000]) (some (8, 9, 6))
    (some (8, 9, 6)) (.next ([1650000000000], [5700000000000]) (some (8, 9, 6)) (some (8, 9, 6))
    (.next ([525000000000], [2325000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
    ([525000000000], [2475000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([900000000000],
    [5850000000000]) (some (8, 9, 6)) (some (9, 9, 6)) (.next ([750000000000], [6000000000000])
    (some (9, 9, 6)) (some (9, 9, 6)) (.next ([150000000000], [1950000000000]) (some (9, 9, 6))
    (some (9, 9, 6)) (.next ([450000000000], [6300000000000]) (some (9, 9, 6)) (some (9, 9, 6))
    (.next ([300000000000], [6300000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next ([0],
    [1950000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next ([-300000000000], [5700000000000])
    (some (9, 9, 6)) (some (9, 9, 6)) (.next ([-450000000000], [6600000000000]) (some (9, 9, 6))
    (some (9, 9, 6)) (.next ([-150000000000], [2100000000000]) (some (9, 9, 6)) (some (9, 9, 6))
    (.next ([-600000000000], [6600000000000]) (some (9, 9, 6)) (some (9, 9, 6))
    fan32Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner5Part0 : FanWitness := (.next ([2640000000000], [4050000000000]) (some (6, 1, 5))
    (some (6, 1, 5)) (.next ([2700000000000, -9000000000000], [4575000000000, 9000000000000]) (some
    (6, 1, 5)) (some (6, 1, 5)) (.next ([1890000000000], [3510000000000]) (some (6, 1, 5)) (some (6,
    1, 5)) (.next ([1500000000000], [4875000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([1350000000000], [4800000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([225000000000,
    -9000000000000], [1125000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0],
    [3765000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-900000000000], [3900000000000])
    (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-1875000000000], [7275000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-1125000000000], [4050000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-75000000000], [225000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-2625000000000], [6390000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2700000000000,
    -9000000000000], [6465000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-2700000000000, -9000000000000], [6390000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-990000000000], [1875000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3000000000000],
    [5490000000000]) (some (0, 2, 5)) (some (0, 2, 6)) (.next ([-2925000000000], [5265000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-3900000000000], [6765000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-4050000000000], [6690000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-4575000000000, -9000000000000], [7275000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-3510000000000], [5400000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-4875000000000], [6375000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-4800000000000],
    [6150000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1125000000000, 0], [1350000000000,
    -9000000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.terminal (some (0, 3, 6)) (some (0, 3, 6))
    (some (0, 3, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner4Part0 : FanWitness := (.next ([0], [3975000000000]) (some (7, 1, 4)) (some (7, 1, 4))
    (.next ([-450000000000], [3600000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
    ([-450000000000], [2175000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([-375000000000],
    [1800000000000]) (some (7, 1, 4)) (some (7, 1, 5)) (.next ([-1950000000000], [7125000000000])
    (some (7, 1, 5)) (some (7, 2, 5)) (.next ([-900000000000], [3150000000000]) (some (7, 2, 5))
    (some (7, 2, 5)) (.next ([-1800000000000], [6000000000000]) (some (7, 2, 5)) (some (7, 2, 5))
    (.next ([-1500000000000], [4950000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
    ([-825000000000], [2700000000000]) (some (7, 2, 5)) (some (7, 2, 6)) (.next ([-1800000000000],
    [5400000000000]) (some (7, 2, 6)) (some (7, 2, 6)) (.next ([-2250000000000], [5400000000000])
    (some (7, 2, 6)) (some (7, 2, 6)) (.next ([-2700000000000], [6450000000000]) (some (7, 2, 6))
    (some (7, 2, 6)) (.next ([-2700000000000], [5850000000000]) (some (7, 2, 6)) (some (7, 2, 6))
    (.next ([-450000000000], [900000000000]) (some (7, 2, 6)) (some (7, 2, 6)) (.next
    ([-1875000000000], [3600000000000]) (some (7, 2, 6)) (some (7, 3, 6)) (.next ([-1425000000000],
    [2700000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-3975000000000], [7425000000000])
    (some (7, 3, 6)) (some (7, 4, 6)) (.next ([-5400000000000], [7725000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-5400000000000], [7125000000000]) (some (7, 4, 6)) (some (7, 4, 6))
    (.next ([-5400000000000], [7050000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-3975000000000], [4950000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-2850000000000],
    [3450000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5850000000000], [6600000000000])
    (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-4950000000000], [5550000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.terminal (some (7, 4, 6)) (some (0, 4, 6)) (some (7, 4,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner4Part0 : FanWitness := (.next ([0], [3975000000000]) (some (7, 1, 4)) (some (7, 1, 4))
    (.next ([-375000000000], [4950000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
    ([-825000000000], [7125000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-450000000000],
    [3600000000000]) (some (0, 1, 4)) (some (0, 1, 7)) (.next ([-450000000000], [2175000000000])
    (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-375000000000], [1800000000000]) (some (0, 1, 7))
    (some (0, 1, 7)) (.next ([-1950000000000], [7125000000000]) (some (0, 1, 7)) (some (0, 2, 7))
    (.next ([-900000000000], [3150000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
    ([-1500000000000], [4950000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-825000000000],
    [2700000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-1800000000000], [5400000000000])
    (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-2250000000000], [5400000000000]) (some (0, 2, 7))
    (some (0, 2, 7)) (.next ([-2700000000000], [5850000000000]) (some (0, 2, 7)) (some (0, 2, 7))
    (.next ([-3975000000000], [8550000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
    ([-450000000000], [900000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-1875000000000],
    [3600000000000]) (some (0, 2, 7)) (some (0, 3, 7)) (.next ([-1425000000000], [2700000000000])
    (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-3975000000000], [7425000000000]) (some (0, 3, 7))
    (some (0, 4, 7)) (.next ([-5400000000000], [8175000000000]) (some (0, 4, 7)) (some (0, 4, 7))
    (.next ([-5850000000000], [7725000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next
    ([-5400000000000], [7125000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next ([-5400000000000],
    [7050000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next ([-3975000000000], [4950000000000])
    (some (0, 4, 7)) (some (0, 4, 7)) (.next ([-5850000000000], [6600000000000]) (some (0, 4, 7))
    (some (0, 4, 7)) (.terminal (some (0, 4, 7)) (some (0, 4, 7)) (some (0, 4,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner4Part0 : FanWitness := (.next ([-540000000000], [4500000000000]) (some (0, 1, 4))
    (some (0, 1, 4)) (.next ([-450000000000], [3600000000000]) (some (0, 1, 4)) (some (0, 1, 7))
    (.next ([-450000000000], [2175000000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next
    ([-375000000000], [1800000000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-1350000000000],
    [6210000000000]) (some (0, 1, 7)) (some (0, 2, 7)) (.next ([-1950000000000], [7125000000000])
    (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-900000000000], [3150000000000]) (some (0, 2, 7))
    (some (0, 2, 7)) (.next ([-1500000000000], [4950000000000]) (some (0, 2, 7)) (some (0, 2, 7))
    (.next ([-825000000000], [2700000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
    ([-1800000000000], [5400000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-2250000000000],
    [5400000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-2235000000000], [4860000000000])
    (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-2700000000000], [5850000000000]) (some (0, 2, 7))
    (some (0, 2, 7)) (.next ([-2775000000000], [5835000000000]) (some (0, 2, 7)) (some (0, 2, 7))
    (.next ([-450000000000], [900000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
    ([-1875000000000], [3600000000000]) (some (0, 2, 7)) (some (0, 3, 7)) (.next ([-1425000000000],
    [2700000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-3975000000000], [7425000000000])
    (some (0, 3, 7)) (some (0, 4, 7)) (.next ([-1410000000000], [2625000000000]) (some (0, 4, 7))
    (some (0, 4, 7)) (.next ([-3225000000000], [5385000000000]) (some (0, 4, 6)) (some (0, 4, 6))
    (.next ([-5400000000000], [7125000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next
    ([-5400000000000], [7050000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-3975000000000],
    [4950000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-5850000000000], [6600000000000])
    (some (0, 4, 6)) (some (0, 4, 6)) (.terminal (some (0, 4, 6)) (some (0, 4, 6)) (some (0, 4,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner4Part1 : FanWitness := (.next ([1725000000000], [450000000000]) (some (6, 1, 4)) (some
    (6, 1, 4)) (.next ([1425000000000], [375000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
    ([4860000000000], [1350000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([5175000000000],
    [1950000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([2250000000000], [900000000000])
    (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3450000000000], [1500000000000]) (some (6, 1, 4))
    (some (6, 1, 4)) (.next ([1875000000000], [825000000000]) (some (6, 1, 4)) (some (6, 1, 4))
    (.next ([3600000000000], [1800000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
    ([3150000000000], [2250000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([2625000000000],
    [2235000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3150000000000], [2700000000000])
    (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3060000000000], [2775000000000]) (some (6, 1, 4))
    (some (6, 1, 4)) (.next ([450000000000], [450000000000]) (some (6, 1, 4)) (some (6, 1, 4))
    (.next ([1725000000000], [1875000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
    ([1275000000000], [1425000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3450000000000],
    [3975000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([1215000000000], [1410000000000])
    (some (6, 1, 4)) (some (6, 1, 4)) (.next ([2160000000000], [3225000000000]) (some (6, 1, 4))
    (some (6, 1, 4)) (.next ([1725000000000], [5400000000000]) (some (6, 1, 4)) (some (6, 1, 4))
    (.next ([1650000000000], [5400000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
    ([975000000000], [3975000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([750000000000],
    [5850000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([0], [3975000000000]) (some (6, 1,
    4)) (some (6, 1, 4)) (.next ([-90000000000], [2325000000000]) (some (0, 1, 4)) (some (0, 1, 4))
    fan35Owner4Part0))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5400000000000], [300000000000]) (some (7, 9, 5))
      (some (7, 9, 5)) (.next ([6150000000000], [450000000000]) (some (7, 9, 5)) (some (7, 9, 6))
      (.next ([1950000000000], [150000000000]) (some (7, 9, 6)) (some (7, 9, 6)) (.next
      ([6000000000000], [600000000000]) (some (7, 9, 6)) (some (7, 9, 6)) (.next ([2625000000000],
      [375000000000]) (some (7, 9, 6)) (some (7, 9, 6)) (.next ([2475000000000], [375000000000])
      (some (7, 9, 6)) (some (7, 9, 6)) (.next ([4800000000000], [1200000000000]) (some (7, 9, 6))
      (some (7, 9, 6)) (.next ([3225000000000], [975000000000]) (some (7, 9, 6)) (some (7, 9, 6))
      (.next ([1275000000000], [975000000000]) (some (7, 9, 6)) (some (7, 9, 6))
      fan32Owner0Part1)))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_5 : ExcludedOn (model32.B 5 ++ [step32.q]) 9000000000000 (model32.caps 5)
    (model32.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3000000000000], [900000000000]) (some (6, 0, 3))
      (some (6, 1, 3)) (.next ([5400000000000], [1875000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      (.next ([2925000000000], [1125000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
      ([150000000000], [75000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([3765000000000],
      [2625000000000]) (some (6, 1, 3)) (some (6, 1, 4)) (.next ([3765000000000, 0], [2700000000000,
      9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3690000000000, -9000000000000],
      [2700000000000, 9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([885000000000],
      [990000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([2490000000000], [3000000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([2340000000000], [2925000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) (.next ([2865000000000], [3900000000000]) (some (6, 1, 4)) (some (6, 1, 5))
      fan32Owner5Part0)))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded32_6 : ExcludedOn (model32.B 6 ++ [step32.q]) 9000000000000 (model32.caps 6)
    (model32.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 3 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_4 : ExcludedOn (model33.B 4 ++ [step33.q]) 9000000000000 (model33.caps 4)
    (model33.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3150000000000], [450000000000]) (some (6, 0, 4))
      (some (6, 1, 4)) (.next ([1725000000000], [450000000000]) (some (6, 1, 4)) (some (6, 1, 4))
      (.next ([1425000000000], [375000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
      ([5175000000000], [1950000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([2250000000000],
      [900000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([4200000000000], [1800000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3450000000000], [1500000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) (.next ([1875000000000], [825000000000]) (some (6, 1, 4)) (some (6, 1, 4))
      (.next ([3600000000000], [1800000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
      ([3150000000000], [2250000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3750000000000],
      [2700000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3150000000000], [2700000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([450000000000], [450000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) (.next ([1725000000000], [1875000000000]) (some (6, 1, 4)) (some (6, 1, 4))
      (.next ([1275000000000], [1425000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
      ([3450000000000], [3975000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([2325000000000],
      [5400000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([1725000000000], [5400000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([1650000000000], [5400000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) (.next ([975000000000], [3975000000000]) (some (6, 1, 4)) (some (6, 1, 4))
      (.next ([600000000000], [2850000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
      ([750000000000], [5850000000000]) (some (6, 1, 4)) (some (7, 1, 4)) (.next ([600000000000],
      [4950000000000]) (some (7, 1, 4)) (some (7, 1, 4)) fan33Owner4Part0))))))))))))))))))))))))
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_5 : ExcludedOn (model33.B 5 ++ [step33.q]) 9000000000000 (model33.caps 5)
    (model33.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_7 : ExcludedOn (model33.B 7 ++ [step33.q]) 9000000000000 (model33.caps 7)
    (model33.ord 7) 0 1 100 := by
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
    · exact excluded33_0
    · exact excluded33_1
    · exact excluded33_2
    · exact excluded33_3
    · exact excluded33_4
    · exact excluded33_5
    · exact excluded33_6
    · exact excluded33_7
    · exact (hj rfl).elim
    · exact excluded33_9
theorem next33 : model33.insert step33 = model34 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded34_0 : ExcludedOn (model34.B 0 ++ [step34.q]) 9000000000000 (model34.caps 0)
    (model34.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_1 : ExcludedOn (model34.B 1 ++ [step34.q]) 9000000000000 (model34.caps 1)
    (model34.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_4 : ExcludedOn (model34.B 4 ++ [step34.q]) 9000000000000 (model34.caps 4)
    (model34.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4575000000000], [375000000000]) (some (7, 0, 4))
      (some (7, 1, 4)) (.next ([6300000000000], [825000000000]) (some (7, 1, 4)) (some (7, 1, 4))
      (.next ([3150000000000], [450000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
      ([1725000000000], [450000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([1425000000000],
      [375000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([5175000000000], [1950000000000])
      (some (7, 1, 4)) (some (7, 1, 4)) (.next ([2250000000000], [900000000000]) (some (7, 1, 4))
      (some (7, 1, 4)) (.next ([3450000000000], [1500000000000]) (some (7, 1, 4)) (some (7, 1, 4))
      (.next ([1875000000000], [825000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
      ([3600000000000], [1800000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([3150000000000],
      [2250000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([3150000000000], [2700000000000])
      (some (7, 1, 4)) (some (7, 1, 4)) (.next ([4575000000000], [3975000000000]) (some (7, 1, 4))
      (some (7, 1, 4)) (.next ([450000000000], [450000000000]) (some (7, 1, 4)) (some (7, 1, 4))
      (.next ([1725000000000], [1875000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
      ([1275000000000], [1425000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([3450000000000],
      [3975000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([2775000000000], [5400000000000])
      (some (7, 1, 4)) (some (7, 1, 4)) (.next ([1875000000000], [5850000000000]) (some (7, 1, 4))
      (some (7, 1, 4)) (.next ([1725000000000], [5400000000000]) (some (7, 1, 4)) (some (7, 1, 4))
      (.next ([1650000000000], [5400000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
      ([975000000000], [3975000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([750000000000],
      [5850000000000]) (some (7, 1, 4)) (some (7, 1, 4)) fan34Owner4Part0))))))))))))))))))))))))
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_7 : ExcludedOn (model34.B 7 ++ [step34.q]) 9000000000000 (model34.caps 7)
    (model34.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_8 : ExcludedOn (model34.B 8 ++ [step34.q]) 9000000000000 (model34.caps 8)
    (model34.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4875000000000], [3525000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([4425000000000], [4575000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([600000000000], [3975000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([300000000000], [4125000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [8400000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3525000000000], [8400000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4575000000000], [9000000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-3975000000000], [4575000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-4125000000000], [4425000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded34_0
    · exact excluded34_1
    · exact excluded34_2
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 6 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

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

theorem excluded35_4 : ExcludedOn (model35.B 4 ++ [step35.q]) 9000000000000 (model35.caps 4)
    (model35.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2235000000000], [90000000000]) (some (6, 0, 4))
      (some (6, 1, 4)) (.next ([3960000000000], [540000000000]) (some (6, 1, 4)) (some (6, 1, 4))
      (.next ([3150000000000], [450000000000]) (some (6, 1, 4)) (some (6, 1, 4))
      fan35Owner4Part1))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_5 : ExcludedOn (model35.B 5 ++ [step35.q]) 9000000000000 (model35.caps 5)
    (model35.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_6 : ExcludedOn (model35.B 6 ++ [step35.q]) 9000000000000 (model35.caps 6)
    (model35.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded35_0
    · exact excluded35_1
    · exact excluded35_2
    · exact (hj rfl).elim
    · exact excluded35_4
    · exact excluded35_5
    · exact excluded35_6
    · exact excluded35_7
    · exact excluded35_8
    · exact excluded35_9
theorem next35 : model35.insert step35 = model36 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint300000310000
end ConwaySoifer.Simplified.Certificates
