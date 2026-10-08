/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext250000252500
import Mathlib.Tactic.FinCases

/-!
# Sext 250000 252500 4

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
namespace Sext250000252500

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner3Part0 : FanWitness := (.next ([2250000000000, 9000000000000], [4575000000000]) (some
    (5, 1, 6)) (some (5, 1, 6)) (.next ([2025000000000], [4575000000000]) (some (5, 1, 6)) (some (5,
    1, 6)) (.next ([1725000000000], [4050000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
    ([1425000000000, 9000000000000], [4875000000000]) (some (5, 1, 6)) (some (5, 2, 6)) (.next
    ([375000000000, 9000000000000], [2250000000000, -9000000000000]) (some (5, 2, 6)) (some (5, 2,
    6)) (.next ([0], [4575000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([-75000000000],
    [2550000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-225000000000, 9000000000000],
    [4275000000000, -9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-525000000000],
    [7050000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-825000000000], [6525000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-825000000000], [4875000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([-600000000000], [2025000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([-1950000000000], [6450000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-2475000000000], [6525000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2250000000000],
    [5925000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1875000000000], [4500000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2100000000000], [3975000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([-525000000000], [825000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([-4350000000000, 9000000000000], [6600000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([-4575000000000, 0], [6825000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([-4575000000000], [6600000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-4050000000000], [5775000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4875000000000,
    0], [6300000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2250000000000,
    9000000000000], [2625000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2, 4))
    (some (0, 2, 4)) (some (0, 2, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner0Part0 : FanWitness := (.next ([-375000000000], [6750000000000]) (some (0, 1, 8))
    (some (0, 1, 8)) (.next ([-750000000000], [7125000000000]) (some (0, 1, 8)) (some (0, 1, 8))
    (.next ([-1125000000000], [7125000000000]) (some (0, 1, 8)) (some (0, 1, 8)) (.next
    ([-1875000000000], [7125000000000]) (some (0, 1, 8)) (some (0, 1, 8)) (.next ([-750000000000],
    [2625000000000]) (some (0, 1, 8)) (some (0, 1, 8)) (.next ([-2250000000000], [7125000000000])
    (some (0, 1, 8)) (some (0, 1, 8)) (.next ([-375000000000], [1125000000000]) (some (0, 1, 8))
    (some (0, 1, 8)) (.next ([-1125000000000], [2625000000000]) (some (0, 1, 8)) (some (0, 1, 8))
    (.next ([-2925000000000], [6300000000000]) (some (0, 1, 8)) (some (0, 1, 8)) (.next
    ([-3300000000000], [7050000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2925000000000],
    [5925000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-3675000000000], [7425000000000])
    (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-750000000000], [1500000000000]) (some (0, 1, 4))
    (some (0, 1, 4)) (.next ([-4425000000000], [7800000000000]) (some (0, 1, 4)) (some (0, 1, 5))
    (.next ([-1500000000000], [2250000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-5550000000000], [7800000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2625000000000],
    [3300000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1500000000000], [1875000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3000000000000], [3675000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-5250000000000], [6000000000000]) (some (0, 1, 5)) (some (0, 8, 5))
    (.next ([-5625000000000], [6375000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next
    ([-5250000000000], [5625000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next ([-5625000000000],
    [6000000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next ([-6375000000000], [6750000000000])
    (some (0, 8, 5)) (some (0, 8, 5)) (.terminal (some (0, 8, 5)) (some (0, 8, 5)) (some (0, 8,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner0Part1 : FanWitness := (.next ([6375000000000], [750000000000]) (some (6, 0, 8)) (some
    (6, 0, 8)) (.next ([6000000000000], [1125000000000]) (some (6, 0, 8)) (some (6, 0, 8)) (.next
    ([5250000000000], [1875000000000]) (some (6, 0, 8)) (some (6, 0, 8)) (.next ([1875000000000],
    [750000000000]) (some (6, 0, 8)) (some (6, 1, 8)) (.next ([4875000000000], [2250000000000])
    (some (6, 1, 8)) (some (6, 1, 8)) (.next ([750000000000], [375000000000]) (some (6, 1, 8)) (some
    (6, 1, 8)) (.next ([1500000000000], [1125000000000]) (some (6, 1, 8)) (some (6, 1, 8)) (.next
    ([3375000000000], [2925000000000]) (some (6, 1, 8)) (some (6, 1, 8)) (.next ([3750000000000],
    [3300000000000]) (some (6, 1, 8)) (some (6, 1, 8)) (.next ([3000000000000], [2925000000000])
    (some (6, 1, 8)) (some (6, 1, 8)) (.next ([3750000000000], [3675000000000]) (some (6, 1, 8))
    (some (6, 1, 8)) (.next ([750000000000], [750000000000]) (some (6, 1, 8)) (some (6, 1, 8))
    (.next ([3375000000000], [4425000000000]) (some (6, 1, 8)) (some (7, 1, 8)) (.next
    ([750000000000], [1500000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([2250000000000],
    [5550000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([675000000000], [2625000000000])
    (some (7, 1, 8)) (some (7, 1, 8)) (.next ([375000000000], [1500000000000]) (some (7, 1, 8))
    (some (7, 1, 8)) (.next ([675000000000], [3000000000000]) (some (7, 1, 8)) (some (7, 1, 8))
    (.next ([750000000000], [5250000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next
    ([750000000000], [5625000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([375000000000],
    [5250000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([375000000000], [5625000000000])
    (some (7, 1, 8)) (some (7, 1, 8)) (.next ([375000000000], [6375000000000]) (some (7, 1, 8))
    (some (7, 1, 8)) (.next ([0], [1125000000000]) (some (7, 1, 8)) (some (7, 1, 8))
    fan33Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner2Part0 : FanWitness := (.next ([-750000000000, 9000000000000], [6375000000000, 0])
    (some (0, 3, 5)) (some (0, 3, 6)) (.next ([-675000000000], [5625000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-750000000000], [5250000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([-150000000000], [975000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-225000000000, 9000000000000], [1125000000000, -9000000000000]) (some (0, 3, 6)) (some (0, 3,
    6)) (.next ([-375000000000], [1500000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-1500000000000], [5475000000000]) (some (0, 3, 6)) (some (0, 4, 6)) (.next ([-1125000000000],
    [3975000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-2625000000000, 9000000000000],
    [6375000000000, 0]) (some (0, 4, 6)) (some (0, 7, 6)) (.next ([-2250000000000, 9000000000000],
    [4875000000000, 0]) (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-3000000000000], [6375000000000])
    (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-1500000000000], [3000000000000]) (some (0, 7, 6))
    (some (0, 7, 6)) (.next ([-4725000000000], [8100000000000]) (some (0, 7, 6)) (some (0, 7, 6))
    (.next ([-4050000000000], [6525000000000]) (some (0, 7, 6)) (some (0, 7, 6)) (.next
    ([-5625000000000, 0], [7875000000000, 9000000000000]) (some (0, 7, 6)) (some (0, 7, 6)) (.next
    ([-2475000000000], [3375000000000]) (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-2250000000000],
    [3000000000000]) (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-4875000000000], [6375000000000])
    (some (0, 7, 6)) (some (1, 7, 6)) (.next ([-3150000000000], [4050000000000]) (some (1, 7, 6))
    (some (1, 7, 6)) (.next ([-1650000000000], [2100000000000]) (some (1, 7, 6)) (some (1, 7, 6))
    (.next ([-4125000000000], [4875000000000]) (some (1, 7, 6)) (some (1, 7, 6)) (.next
    ([-900000000000], [1050000000000]) (some (1, 7, 6)) (some (1, 7, 6)) (.next ([-4500000000000],
    [4875000000000]) (some (1, 7, 6)) (some (2, 7, 6)) (.next ([-5475000000000], [5850000000000])
    (some (2, 7, 6)) (some (2, 7, 6)) (.terminal (some (2, 7, 6)) (some (2, 7, 0)) (some (2, 7,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner2Part1 : FanWitness := (.next ([4950000000000], [675000000000]) (some (0, 2, 7)) (some
    (0, 2, 7)) (.next ([4500000000000], [750000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
    ([825000000000], [150000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([900000000000, 0],
    [225000000000, -9000000000000]) (some (0, 2, 7)) (some (0, 3, 7)) (.next ([1125000000000],
    [375000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([3975000000000], [1500000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([2850000000000], [1125000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([3750000000000, 9000000000000], [2625000000000, -9000000000000]) (some
    (0, 3, 5)) (some (0, 3, 5)) (.next ([2625000000000, 9000000000000], [2250000000000,
    -9000000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([3375000000000], [3000000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([1500000000000], [1500000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([3375000000000], [4725000000000]) (some (0, 3, 5)) (some (0, 3, 5))
    (.next ([2475000000000], [4050000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([2250000000000, 9000000000000], [5625000000000, 0]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([900000000000], [2475000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([750000000000],
    [2250000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([1500000000000], [4875000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([900000000000], [3150000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([450000000000], [1650000000000]) (some (0, 3, 5)) (some (0, 3, 5))
    (.next ([750000000000], [4125000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([150000000000], [900000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([375000000000],
    [4500000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([375000000000], [5475000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([0], [5625000000000]) (some (0, 3, 5)) (some (0, 3,
    5)) fan34Owner2Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner2Part0 : FanWitness := (.next ([0], [5625000000000]) (some (0, 3, 7)) (some (0, 3, 7))
    (.next ([-750000000000, 9000000000000], [6375000000000, 0]) (some (0, 3, 7)) (some (0, 3, 7))
    (.next ([-750000000000], [5250000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
    ([-150000000000], [975000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-375000000000],
    [1500000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-1800000000000, 9000000000000],
    [6525000000000, 0]) (some (0, 3, 7)) (some (0, 4, 7)) (.next ([-3000000000000], [8850000000000])
    (some (0, 4, 7)) (some (0, 4, 7)) (.next ([-2625000000000, 9000000000000], [6375000000000, 0])
    (some (0, 4, 7)) (some (0, 4, 7)) (.next ([-4050000000000], [9000000000000]) (some (0, 4, 7))
    (some (0, 4, 7)) (.next ([-2250000000000, 9000000000000], [4875000000000, 0]) (some (0, 4, 7))
    (some (0, 4, 7)) (.next ([-3000000000000], [6375000000000]) (some (0, 4, 7)) (some (0, 5, 7))
    (.next ([-1500000000000], [3000000000000]) (some (0, 5, 7)) (some (0, 5, 7)) (.next
    ([-4875000000000], [8850000000000]) (some (0, 5, 7)) (some (0, 5, 7)) (.next ([-4500000000000],
    [7350000000000]) (some (0, 5, 7)) (some (0, 5, 7)) (.next ([-4050000000000], [6525000000000])
    (some (0, 5, 7)) (some (0, 5, 7)) (.next ([-5625000000000, 0], [7875000000000, 9000000000000])
    (some (0, 5, 7)) (some (0, 5, 7)) (.next ([-2250000000000], [3000000000000]) (some (0, 5, 7))
    (some (0, 5, 7)) (.next ([-4875000000000], [6375000000000]) (some (0, 5, 7)) (some (1, 5, 7))
    (.next ([-3150000000000], [4050000000000]) (some (1, 5, 7)) (some (1, 5, 7)) (.next
    ([-1650000000000], [2100000000000]) (some (1, 5, 7)) (some (1, 5, 7)) (.next ([-4125000000000],
    [4875000000000]) (some (1, 5, 7)) (some (1, 5, 7)) (.next ([-900000000000], [1050000000000])
    (some (1, 5, 7)) (some (1, 5, 7)) (.next ([-2250000000000, -9000000000000], [2475000000000, 0])
    (some (1, 5, 7)) (some (2, 5, 7)) (.next ([-4500000000000], [4875000000000]) (some (2, 5, 7))
    (some (2, 7, 7)) (.terminal (some (2, 7, 7)) (some (2, 7, 0)) (some (2, 7,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner2Part0 : FanWitness := (.next ([0], [5625000000000]) (some (0, 3, 7)) (some (0, 3, 7))
    (.next ([-375000000000], [6375000000000]) (some (0, 3, 5)) (some (0, 3, 6)) (.next
    ([-750000000000, 9000000000000], [6375000000000, 0]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-750000000000], [5250000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-150000000000],
    [975000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-1425000000000], [6525000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-375000000000], [1500000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-1800000000000, 9000000000000], [6525000000000, 0]) (some (0, 3, 6))
    (some (0, 4, 6)) (.next ([-2250000000000], [6375000000000]) (some (0, 4, 6)) (some (0, 4, 6))
    (.next ([-1875000000000], [4875000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next
    ([-2625000000000, 9000000000000], [6375000000000, 0]) (some (0, 4, 6)) (some (0, 7, 6)) (.next
    ([-2250000000000, 9000000000000], [4875000000000, 0]) (some (0, 7, 6)) (some (0, 7, 6)) (.next
    ([-3000000000000], [6375000000000]) (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-1500000000000],
    [3000000000000]) (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-4050000000000], [6525000000000])
    (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-5625000000000], [8250000000000]) (some (0, 7, 6))
    (some (0, 7, 6)) (.next ([-5625000000000, 0], [7875000000000, 9000000000000]) (some (0, 7, 6))
    (some (0, 7, 6)) (.next ([-2250000000000], [3000000000000]) (some (0, 7, 6)) (some (0, 7, 6))
    (.next ([-4875000000000], [6375000000000]) (some (0, 7, 6)) (some (1, 7, 6)) (.next
    ([-3150000000000], [4050000000000]) (some (1, 7, 6)) (some (1, 7, 6)) (.next ([-1650000000000],
    [2100000000000]) (some (1, 7, 6)) (some (1, 7, 6)) (.next ([-4125000000000], [4875000000000])
    (some (1, 7, 6)) (some (1, 7, 6)) (.next ([-900000000000], [1050000000000]) (some (1, 7, 6))
    (some (1, 7, 6)) (.next ([-4500000000000], [4875000000000]) (some (1, 7, 6)) (some (2, 7, 6))
    (.terminal (some (2, 7, 6)) (some (2, 7, 0)) (some (2, 7, 6)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 400 := by
  apply ExclusionHint.sound (.pair 1 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded32_1 : ExcludedOn (model32.B 1 ++ [step32.q]) 9000000000000 (model32.caps 1)
    (model32.ord 1) 0 1 400 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded32_3 : ExcludedOn (model32.B 3 ++ [step32.q]) 9000000000000 (model32.caps 3)
    (model32.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2475000000000], [75000000000]) (some (4, 0, 2))
      (some (5, 0, 2)) (.next ([4050000000000, 0], [225000000000, -9000000000000]) (some (5, 0, 2))
      (some (5, 0, 6)) (.next ([6525000000000], [525000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([5700000000000], [825000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([4050000000000], [825000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1425000000000],
      [600000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([4500000000000], [1950000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([4050000000000], [2475000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([3675000000000], [2250000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([2625000000000], [1875000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([1875000000000], [2100000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([300000000000],
      [525000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([2250000000000, 9000000000000],
      [4350000000000, -9000000000000]) (some (5, 0, 6)) (some (5, 1, 6))
      fan32Owner3Part0)))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded32_4 : ExcludedOn (model32.B 4 ++ [step32.q]) 9000000000000 (model32.caps 4)
    (model32.ord 4) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded32_5 : ExcludedOn (model32.B 5 ++ [step32.q]) 9000000000000 (model32.caps 5)
    (model32.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded32_6 : ExcludedOn (model32.B 6 ++ [step32.q]) 9000000000000 (model32.caps 6)
    (model32.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded32_7 : ExcludedOn (model32.B 7 ++ [step32.q]) 9000000000000 (model32.caps 7)
    (model32.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded32_8 : ExcludedOn (model32.B 8 ++ [step32.q]) 9000000000000 (model32.caps 8)
    (model32.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded32_9 : ExcludedOn (model32.B 9 ++ [step32.q]) 9000000000000 (model32.caps 9)
    (model32.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked32 : StepValid model32 9000000000000 step32 0 1 400 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded32_0
    · exact excluded32_1
    · exact (hj rfl).elim
    · exact excluded32_3
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
    (model33.ord 0) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6375000000000], [375000000000]) (some (5, 0, 8))
      (some (6, 0, 8)) fan33Owner0Part1)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded33_2 : ExcludedOn (model33.B 2 ++ [step33.q]) 9000000000000 (model33.caps 2)
    (model33.ord 2) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded33_3 : ExcludedOn (model33.B 3 ++ [step33.q]) 9000000000000 (model33.caps 3)
    (model33.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded33_4 : ExcludedOn (model33.B 4 ++ [step33.q]) 9000000000000 (model33.caps 4)
    (model33.ord 4) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded33_5 : ExcludedOn (model33.B 5 ++ [step33.q]) 9000000000000 (model33.caps 5)
    (model33.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6300000000000, 9000000000000], [75000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([2325000000000], [375000000000,
      -9000000000000]) (some (2, 0, 2)) (some (2, 0, 2)) (.next ([4050000000000], [2325000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([2250000000000, 9000000000000], [6750000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [2250000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-75000000000, 9000000000000],
      [6375000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-375000000000, 9000000000000],
      [2700000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2325000000000],
      [6375000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6750000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded33_7 : ExcludedOn (model33.B 7 ++ [step33.q]) 9000000000000 (model33.caps 7)
    (model33.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded33_8 : ExcludedOn (model33.B 8 ++ [step33.q]) 9000000000000 (model33.caps 8)
    (model33.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded33_9 : ExcludedOn (model33.B 9 ++ [step33.q]) 9000000000000 (model33.caps 9)
    (model33.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked33 : StepValid model33 9000000000000 step33 0 1 400 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded33_0
    · exact (hj rfl).elim
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

theorem excluded34_0 : ExcludedOn (model34.B 0 ++ [step34.q]) 9000000000000 (model34.caps 0)
    (model34.ord 0) 0 1 400 := by
  apply ExclusionHint.sound (.pair 1 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5625000000000, 9000000000000], [750000000000,
      -9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) fan34Owner2Part1)) (den := 9000000000000)
      (fuel := 12)
      (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded34_3 : ExcludedOn (model34.B 3 ++ [step34.q]) 9000000000000 (model34.caps 3)
    (model34.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded34_4 : ExcludedOn (model34.B 4 ++ [step34.q]) 9000000000000 (model34.caps 4)
    (model34.ord 4) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded34_7 : ExcludedOn (model34.B 7 ++ [step34.q]) 9000000000000 (model34.caps 7)
    (model34.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6525000000000], [1125000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([6525000000000], [3375000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([2250000000000, 9000000000000], [3450000000000, -9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([825000000000], [3375000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([0], [5700000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next
      ([-1125000000000, 9000000000000], [7650000000000, -9000000000000]) (some (3, 3, 2)) (some (3,
      3, 2)) (.next ([-3375000000000], [9900000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-3450000000000, 9000000000000], [5700000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-3375000000000], [4200000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded34_8 : ExcludedOn (model34.B 8 ++ [step34.q]) 9000000000000 (model34.caps 8)
    (model34.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded34_9 : ExcludedOn (model34.B 9 ++ [step34.q]) 9000000000000 (model34.caps 9)
    (model34.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked34 : StepValid model34 9000000000000 step34 0 1 400 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded34_0
    · exact (hj rfl).elim
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
    (model35.ord 0) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded35_1 : ExcludedOn (model35.B 1 ++ [step35.q]) 9000000000000 (model35.caps 1)
    (model35.ord 1) 0 1 400 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded35_2 : ExcludedOn (model35.B 2 ++ [step35.q]) 9000000000000 (model35.caps 2)
    (model35.ord 2) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5625000000000, 9000000000000], [750000000000,
      -9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([4500000000000], [750000000000])
      (some (0, 2, 7)) (some (0, 2, 7)) (.next ([825000000000], [150000000000]) (some (0, 2, 7))
      (some (0, 2, 7)) (.next ([1125000000000], [375000000000]) (some (0, 2, 7)) (some (0, 3, 7))
      (.next ([4725000000000, 9000000000000], [1800000000000, -9000000000000]) (some (0, 3, 7))
      (some (0, 3, 7)) (.next ([5850000000000], [3000000000000]) (some (0, 3, 7)) (some (0, 3, 7))
      (.next ([3750000000000, 9000000000000], [2625000000000, -9000000000000]) (some (0, 3, 7))
      (some (0, 3, 7)) (.next ([4950000000000], [4050000000000]) (some (0, 3, 7)) (some (0, 3, 7))
      (.next ([2625000000000, 9000000000000], [2250000000000, -9000000000000]) (some (0, 3, 7))
      (some (0, 3, 7)) (.next ([3375000000000], [3000000000000]) (some (0, 3, 7)) (some (0, 3, 7))
      (.next ([1500000000000], [1500000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
      ([3975000000000], [4875000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([2850000000000],
      [4500000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([2475000000000], [4050000000000])
      (some (0, 3, 7)) (some (0, 3, 7)) (.next ([2250000000000, 9000000000000], [5625000000000, 0])
      (some (0, 3, 7)) (some (0, 3, 7)) (.next ([750000000000], [2250000000000]) (some (0, 3, 7))
      (some (0, 3, 7)) (.next ([1500000000000], [4875000000000]) (some (0, 3, 7)) (some (0, 3, 7))
      (.next ([900000000000], [3150000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
      ([450000000000], [1650000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([750000000000],
      [4125000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([150000000000], [900000000000])
      (some (0, 3, 7)) (some (0, 3, 7)) (.next ([225000000000, -9000000000000], [2250000000000,
      9000000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([375000000000], [4500000000000])
      (some (0, 3, 7)) (some (0, 3, 7)) fan35Owner2Part0)))))))))))))))))))))))) (den :=
      9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded35_3 : ExcludedOn (model35.B 3 ++ [step35.q]) 9000000000000 (model35.caps 3)
    (model35.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded35_4 : ExcludedOn (model35.B 4 ++ [step35.q]) 9000000000000 (model35.caps 4)
    (model35.ord 4) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded35_5 : ExcludedOn (model35.B 5 ++ [step35.q]) 9000000000000 (model35.caps 5)
    (model35.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded35_6 : ExcludedOn (model35.B 6 ++ [step35.q]) 9000000000000 (model35.caps 6)
    (model35.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded35_8 : ExcludedOn (model35.B 8 ++ [step35.q]) 9000000000000 (model35.caps 8)
    (model35.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded35_9 : ExcludedOn (model35.B 9 ++ [step35.q]) 9000000000000 (model35.caps 9)
    (model35.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked35 : StepValid model35 9000000000000 step35 0 1 400 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded35_0
    · exact excluded35_1
    · exact excluded35_2
    · exact excluded35_3
    · exact excluded35_4
    · exact excluded35_5
    · exact excluded35_6
    · exact (hj rfl).elim
    · exact excluded35_8
    · exact excluded35_9
theorem next35 : model35.insert step35 = model36 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded36_0 : ExcludedOn (model36.B 0 ++ [step36.q]) 9000000000000 (model36.caps 0)
    (model36.ord 0) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded36_1 : ExcludedOn (model36.B 1 ++ [step36.q]) 9000000000000 (model36.caps 1)
    (model36.ord 1) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2325000000000], [375000000000, -9000000000000])
      (some (0, 1, 2)) (some (0, 1, 5)) (.next ([3375000000000, -9000000000000], [900000000000, 0])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([2250000000000, 9000000000000], [1800000000000,
      -9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([2250000000000, 9000000000000],
      [2250000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([4050000000000],
      [4200000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([2325000000000], [2625000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([2325000000000], [6675000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([1575000000000], [4950000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([1350000000000, 9000000000000], [6525000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([75000000000, -9000000000000], [4875000000000, 9000000000000]) (some (0, 1, 5)) (some
      (0, 1, 5)) (.next ([0], [2250000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([-375000000000, 9000000000000], [2700000000000, -9000000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([-900000000000, 0], [4275000000000, -9000000000000]) (some (0, 1, 5))
      (some (0, 2, 5)) (.next ([-1800000000000, 9000000000000], [4050000000000, 0]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([-2250000000000, -9000000000000], [4500000000000, 18000000000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4200000000000], [8250000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([-2625000000000], [4950000000000]) (some (0, 2, 5)) (some (1, 2, 5))
      (.next ([-6675000000000], [9000000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next
      ([-4950000000000], [6525000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next
      ([-6525000000000], [7875000000000, 9000000000000]) (some (1, 2, 0)) (some (1, 2, 0)) (.next
      ([-4875000000000, -9000000000000], [4950000000000, 0]) (some (1, 2, 0)) (some (1, 2, 0))
      (.terminal (some (1, 2, 0)) (some (1, 2, 0)) (some (1, 2, 0))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded36_2 : ExcludedOn (model36.B 2 ++ [step36.q]) 9000000000000 (model36.caps 2)
    (model36.ord 2) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded36_3 : ExcludedOn (model36.B 3 ++ [step36.q]) 9000000000000 (model36.caps 3)
    (model36.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded36_4 : ExcludedOn (model36.B 4 ++ [step36.q]) 9000000000000 (model36.caps 4)
    (model36.ord 4) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded36_6 : ExcludedOn (model36.B 6 ++ [step36.q]) 9000000000000 (model36.caps 6)
    (model36.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded36_8 : ExcludedOn (model36.B 8 ++ [step36.q]) 9000000000000 (model36.caps 8)
    (model36.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded36_9 : ExcludedOn (model36.B 9 ++ [step36.q]) 9000000000000 (model36.caps 9)
    (model36.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked36 : StepValid model36 9000000000000 step36 0 1 400 := by
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
    · exact excluded36_4
    · exact excluded36_5
    · exact excluded36_6
    · exact (hj rfl).elim
    · exact excluded36_8
    · exact excluded36_9
theorem next36 : model36.insert step36 = model37 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded37_1 : ExcludedOn (model37.B 1 ++ [step37.q]) 9000000000000 (model37.caps 1)
    (model37.ord 1) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2325000000000], [375000000000, -9000000000000])
      (some (5, 1, 2)) (some (5, 1, 3)) (.next ([3375000000000, -9000000000000], [900000000000, 0])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4950000000000], [4050000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([2250000000000, 9000000000000], [2250000000000, 9000000000000]) (some
      (5, 1, 3)) (some (5, 1, 3)) (.next ([4050000000000], [4200000000000]) (some (5, 1, 3)) (some
      (5, 1, 3)) (.next ([2325000000000], [2625000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([2250000000000, 9000000000000], [6375000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([1350000000000, 9000000000000], [6525000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([150000000000], [750000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([75000000000,
      -9000000000000], [4875000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([0], [2250000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-375000000000, 9000000000000], [2700000000000, -9000000000000]) (some (0, 1, 3)) (some (0,
      1, 5)) (.next ([-900000000000, 0], [4275000000000, -9000000000000]) (some (0, 1, 5)) (some (0,
      2, 5)) (.next ([-4050000000000], [9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-2250000000000, -9000000000000], [4500000000000, 18000000000000]) (some (0, 2, 5)) (some (0,
      2, 5)) (.next ([-4200000000000], [8250000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-2625000000000], [4950000000000]) (some (0, 2, 5)) (some (1, 2, 5)) (.next
      ([-6375000000000], [8625000000000, 9000000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next
      ([-6525000000000], [7875000000000, 9000000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next
      ([-750000000000], [900000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next ([-4875000000000,
      -9000000000000], [4950000000000, 0]) (some (1, 2, 5)) (some (1, 2, 5)) (.terminal (some (1, 2,
      5)) (some (1, 2, 5)) (some (1, 2, 5))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded37_2 : ExcludedOn (model37.B 2 ++ [step37.q]) 9000000000000 (model37.caps 2)
    (model37.ord 2) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6000000000000], [375000000000]) (some (0, 2, 7))
      (some (0, 2, 7)) (.next ([5625000000000, 9000000000000], [750000000000, -9000000000000]) (some
      (0, 2, 7)) (some (0, 2, 7)) (.next ([4500000000000], [750000000000]) (some (0, 2, 7)) (some
      (0, 2, 7)) (.next ([825000000000], [150000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
      ([5100000000000], [1425000000000]) (some (0, 2, 7)) (some (0, 3, 7)) (.next ([1125000000000],
      [375000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([4725000000000, 9000000000000],
      [1800000000000, -9000000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([4125000000000],
      [2250000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([3000000000000], [1875000000000])
      (some (0, 3, 7)) (some (0, 3, 7)) (.next ([3750000000000, 9000000000000], [2625000000000,
      -9000000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([2625000000000, 9000000000000],
      [2250000000000, -9000000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([3375000000000],
      [3000000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([1500000000000], [1500000000000])
      (some (0, 3, 7)) (some (0, 3, 7)) (.next ([2475000000000], [4050000000000]) (some (0, 3, 7))
      (some (0, 3, 7)) (.next ([2625000000000], [5625000000000]) (some (0, 3, 7)) (some (0, 3, 7))
      (.next ([2250000000000, 9000000000000], [5625000000000, 0]) (some (0, 3, 7)) (some (0, 3, 7))
      (.next ([750000000000], [2250000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
      ([1500000000000], [4875000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([900000000000],
      [3150000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([450000000000], [1650000000000])
      (some (0, 3, 7)) (some (0, 3, 7)) (.next ([750000000000], [4125000000000]) (some (0, 3, 7))
      (some (0, 3, 7)) (.next ([150000000000], [900000000000]) (some (0, 3, 7)) (some (0, 3, 7))
      (.next ([375000000000], [4500000000000]) (some (0, 3, 7)) (some (0, 3, 7))
      fan37Owner2Part0)))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded37_3 : ExcludedOn (model37.B 3 ++ [step37.q]) 9000000000000 (model37.caps 3)
    (model37.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded37_4 : ExcludedOn (model37.B 4 ++ [step37.q]) 9000000000000 (model37.caps 4)
    (model37.ord 4) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded37_5 : ExcludedOn (model37.B 5 ++ [step37.q]) 9000000000000 (model37.caps 5)
    (model37.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded37_6 : ExcludedOn (model37.B 6 ++ [step37.q]) 9000000000000 (model37.caps 6)
    (model37.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded37_7 : ExcludedOn (model37.B 7 ++ [step37.q]) 9000000000000 (model37.caps 7)
    (model37.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2475000000000], [150000000000]) (some (0, 3, 1))
      (some (0, 3, 2)) (.next ([4950000000000], [1575000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([6375000000000], [2625000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next
      ([2325000000000], [4050000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0],
      [6525000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-150000000000], [2625000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1575000000000], [6525000000000]) (some (0, 1, 2))
      (some (3, 1, 2)) (.next ([-2625000000000], [9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-4050000000000], [6375000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some
      (3, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded37_8 : ExcludedOn (model37.B 8 ++ [step37.q]) 9000000000000 (model37.caps 8)
    (model37.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded37_9 : ExcludedOn (model37.B 9 ++ [step37.q]) 9000000000000 (model37.caps 9)
    (model37.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked37 : StepValid model37 9000000000000 step37 0 1 400 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded37_1
    · exact excluded37_2
    · exact excluded37_3
    · exact excluded37_4
    · exact excluded37_5
    · exact excluded37_6
    · exact excluded37_7
    · exact excluded37_8
    · exact excluded37_9
theorem next37 : model37.insert step37 = model38 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext250000252500
end ConwaySoifer.Simplified.Certificates
