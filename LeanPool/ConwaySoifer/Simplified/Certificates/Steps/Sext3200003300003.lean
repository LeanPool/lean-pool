/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext320000330000
import Mathlib.Tactic.FinCases

/-!
# Sext 320000 330000 3

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
namespace Sext320000330000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner4Part0 : FanWitness := (.next ([2880000000000, 9000000000000], [3495000000000]) (some
    (6, 1, 3)) (some (6, 1, 3)) (.next ([2250000000000], [2934000000000]) (some (6, 1, 3)) (some (6,
    1, 3)) (.next ([684000000000], [936000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([750000000000], [1554000000000, -9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([1170000000000], [3495000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([519000000000],
    [2415000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([750000000000], [4434000000000])
    (some (5, 1, 3)) (some (5, 1, 3)) (.next ([519000000000], [3915000000000]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([375000000000], [5745000000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([0], [3495000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-1245000000000],
    [6429000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-936000000000], [3120000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2745000000000], [7929000000000]) (some (0, 1, 3))
    (some (0, 1, 6)) (.next ([-795000000000], [2250000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-2250000000000], [6120000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-3495000000000], [6375000000000, 9000000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-2934000000000], [5184000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-936000000000],
    [1620000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-1554000000000, 9000000000000],
    [2304000000000, -9000000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-3495000000000],
    [4665000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-2415000000000], [2934000000000])
    (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-4434000000000], [5184000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-3915000000000], [4434000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-5745000000000], [6120000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.terminal (some
    (0, 2, 6)) (some (0, 2, 6)) (some (0, 2, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner2Part0 : FanWitness := (.next ([2250000000000], [3870000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([2880000000000, 9000000000000], [5460000000000, 0]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([1995000000000], [4125000000000]) (some (6, 2, 4)) (some (6, 2, 4))
    (.next ([1170000000000], [2670000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([660000000000], [3210000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([660000000000],
    [3465000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([285000000000], [3840000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([0], [2955000000000]) (some (6, 2, 4)) (some (6, 2,
    4)) (.next ([-30000000000], [1995000000000]) (some (6, 2, 4)) (some (6, 2, 5)) (.next
    ([-285000000000], [1995000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-990000000000,
    9000000000000], [6120000000000, 0]) (some (6, 2, 5)) (some (6, 3, 5)) (.next ([-705000000000],
    [3870000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-1245000000000, 9000000000000],
    [6120000000000, 0]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-960000000000, 9000000000000],
    [4125000000000, 0]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-960000000000], [4125000000000])
    (some (6, 3, 5)) (some (6, 4, 5)) (.next ([-1335000000000], [5175000000000]) (some (6, 4, 5))
    (some (6, 4, 5)) (.next ([-2955000000000, 0], [5835000000000, 9000000000000]) (some (6, 4, 5))
    (some (6, 4, 5)) (.next ([-3870000000000], [6120000000000]) (some (6, 4, 5)) (some (6, 4, 5))
    (.next ([-5460000000000, 0], [8340000000000, 9000000000000]) (some (6, 4, 5)) (some (6, 4, 5))
    (.next ([-4125000000000], [6120000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next
    ([-2670000000000], [3840000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-3210000000000],
    [3870000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-3465000000000], [4125000000000])
    (some (1, 4, 5)) (some (1, 4, 5)) (.next ([-3840000000000], [4125000000000]) (some (1, 4, 5))
    (some (1, 4, 5)) (.terminal (some (1, 4, 5)) (some (1, 4, 0)) (some (1, 4,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan26Owner2Part0 : FanWitness := (.next ([2250000000000], [3870000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([1995000000000], [4125000000000]) (some (6, 2, 4)) (some (6, 2, 4))
    (.next ([2439000000000, 9000000000000], [5625000000000, 0]) (some (6, 2, 4)) (some (6, 2, 4))
    (.next ([495000000000], [2934000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([495000000000], [3189000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([285000000000],
    [3840000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([0], [2955000000000]) (some (6, 2,
    4)) (some (6, 2, 4)) (.next ([-30000000000], [1995000000000]) (some (6, 2, 4)) (some (6, 2, 5))
    (.next ([-441000000000], [5625000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next
    ([-285000000000], [1995000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-990000000000,
    9000000000000], [6120000000000, 0]) (some (6, 2, 5)) (some (6, 3, 5)) (.next ([-441000000000],
    [2670000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-705000000000], [3870000000000])
    (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-1245000000000, 9000000000000], [6120000000000, 0])
    (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-960000000000, 9000000000000], [4125000000000, 0])
    (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-960000000000], [4125000000000]) (some (6, 3, 5))
    (some (6, 4, 5)) (.next ([-1500000000000], [4899000000000]) (some (6, 4, 5)) (some (6, 4, 5))
    (.next ([-2955000000000, 0], [5835000000000, 9000000000000]) (some (6, 4, 5)) (some (6, 4, 5))
    (.next ([-3870000000000], [6120000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next
    ([-4125000000000], [6120000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-5625000000000,
    0], [8064000000000, 9000000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-2934000000000],
    [3429000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-3189000000000], [3684000000000])
    (some (1, 4, 5)) (some (1, 4, 5)) (.next ([-3840000000000], [4125000000000]) (some (1, 4, 5))
    (some (1, 4, 5)) (.terminal (some (1, 4, 5)) (some (1, 4, 0)) (some (1, 4,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner3Part0 : FanWitness := (.next ([3540000000000], [2880000000000, 9000000000000]) (some
    (6, 1, 3)) (some (6, 1, 3)) (.next ([3285000000000, -9000000000000], [2880000000000,
    9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([3066000000000], [4125000000000])
    (some (6, 1, 3)) (some (6, 1, 3)) (.next ([2790000000000], [4566000000000]) (some (6, 1, 3))
    (some (6, 1, 3)) (.next ([165000000000], [276000000000]) (some (6, 1, 3)) (some (6, 1, 3))
    (.next ([1599000000000], [3816000000000]) (some (6, 1, 3)) (some (6, 1, 4)) (.next
    ([441000000000], [3375000000000]) (some (6, 1, 4)) (some (6, 2, 4)) (.next ([441000000000],
    [3570000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([0], [2880000000000, 9000000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-195000000000], [6360000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([-195000000000], [2880000000000, 9000000000000]) (some (6, 2, 4)) (some
    (6, 2, 4)) (.next ([-750000000000], [4566000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-945000000000], [4566000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2439000000000,
    -9000000000000], [6255000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-2349000000000], [5724000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2625000000000],
    [6165000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2880000000000, -9000000000000],
    [6420000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2880000000000,
    -9000000000000], [6165000000000]) (some (0, 2, 4)) (some (1, 2, 4)) (.next ([-4125000000000],
    [7191000000000]) (some (1, 2, 4)) (some (1, 2, 4)) (.next ([-4566000000000], [7356000000000])
    (some (1, 2, 4)) (some (1, 2, 4)) (.next ([-276000000000], [441000000000]) (some (1, 2, 4))
    (some (1, 2, 4)) (.next ([-3816000000000], [5415000000000]) (some (1, 2, 4)) (some (1, 2, 4))
    (.next ([-3375000000000], [3816000000000]) (some (1, 2, 4)) (some (1, 2, 4)) (.next
    ([-3570000000000], [4011000000000]) (some (1, 2, 4)) (some (1, 2, 4)) (.terminal (some (1, 2,
    4)) (some (1, 2, 4)) (some (1, 2, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner4Part0 : FanWitness := (.next ([1455000000000], [795000000000]) (some (6, 1, 2)) (some
    (6, 1, 2)) (.next ([3870000000000], [2250000000000]) (some (6, 1, 2)) (some (6, 1, 3)) (.next
    ([2370000000000], [1500000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4620000000000],
    [3495000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([2880000000000, 9000000000000],
    [3495000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([2250000000000], [2934000000000])
    (some (6, 1, 3)) (some (6, 1, 3)) (.next ([684000000000], [936000000000]) (some (6, 1, 3)) (some
    (6, 1, 3)) (.next ([1170000000000], [3495000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([519000000000], [2415000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([375000000000],
    [5745000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([0], [3495000000000]) (some (6, 1,
    3)) (some (6, 1, 3)) (.next ([-45000000000], [4665000000000]) (some (0, 1, 3)) (some (0, 1, 3))
    (.next ([-1245000000000], [6429000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-564000000000], [2250000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-795000000000],
    [2250000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2250000000000], [6120000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1500000000000], [3870000000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([-3495000000000], [8115000000000]) (some (0, 1, 3)) (some (0, 1, 6))
    (.next ([-3495000000000], [6375000000000, 9000000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-2934000000000], [5184000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-936000000000], [1620000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-3495000000000],
    [4665000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-2415000000000], [2934000000000])
    (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-5745000000000], [6120000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.terminal (some (0, 2, 6)) (some (0, 2, 6)) (some (0, 2,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan29Owner3Part0 : FanWitness := (.next ([3840000000000], [2535000000000]) (some (4, 0, 5))
    (some (4, 0, 5)) (.next ([3375000000000], [2349000000000]) (some (4, 0, 5)) (some (4, 0, 5))
    (.next ([3540000000000], [2625000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
    ([3816000000000], [3939000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([3540000000000],
    [4380000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([165000000000], [276000000000]) (some
    (4, 0, 5)) (some (4, 0, 5)) (.next ([1785000000000], [4380000000000]) (some (4, 0, 5)) (some (4,
    0, 5)) (.next ([1005000000000], [2835000000000]) (some (4, 0, 5)) (some (4, 1, 5)) (.next
    ([840000000000], [2559000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([441000000000],
    [3375000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([210000000000], [2325000000000])
    (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0], [4380000000000]) (some (4, 1, 3)) (some (4, 1,
    3)) (.next ([-540000000000], [6915000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-2535000000000], [6375000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2349000000000],
    [5724000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2625000000000], [6165000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3939000000000], [7755000000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([-4380000000000], [7920000000000]) (some (0, 1, 3)) (some (0, 1, 3))
    (.next ([-276000000000], [441000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-4380000000000], [6165000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2835000000000],
    [3840000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2559000000000], [3399000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3375000000000], [3816000000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([-2325000000000], [2535000000000]) (some (0, 1, 3)) (some (0, 1, 3))
    (.terminal (some (0, 1, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan30Owner2Part0 : FanWitness := (.next ([285000000000], [345000000000]) (some (6, 1, 4)) (some
    (6, 1, 4)) (.next ([2625000000000], [3840000000000]) (some (6, 1, 4)) (some (6, 2, 4)) (.next
    ([2880000000000, 9000000000000], [5340000000000, 0]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([1995000000000], [4125000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([1170000000000],
    [2670000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([1125000000000], [2715000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([780000000000], [3345000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([285000000000], [3840000000000]) (some (6, 2, 4)) (some (6, 2, 4))
    (.next ([0], [2955000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-330000000000],
    [3840000000000]) (some (6, 2, 4)) (some (6, 2, 5)) (.next ([-960000000000, 9000000000000],
    [6465000000000, 0]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-1245000000000, 9000000000000],
    [6120000000000, 0]) (some (6, 2, 5)) (some (6, 3, 5)) (.next ([-960000000000, 9000000000000],
    [4125000000000, 0]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-960000000000], [4125000000000])
    (some (6, 3, 5)) (some (6, 4, 5)) (.next ([-1215000000000], [5055000000000]) (some (6, 4, 5))
    (some (6, 4, 5)) (.next ([-2955000000000, 0], [5835000000000, 9000000000000]) (some (6, 4, 5))
    (some (6, 4, 5)) (.next ([-345000000000], [630000000000]) (some (6, 4, 5)) (some (6, 4, 5))
    (.next ([-3840000000000], [6465000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next
    ([-5340000000000, 0], [8220000000000, 9000000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next
    ([-4125000000000], [6120000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-2670000000000],
    [3840000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-2715000000000], [3840000000000])
    (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-3345000000000], [4125000000000]) (some (1, 4, 5))
    (some (1, 4, 5)) (.next ([-3840000000000], [4125000000000]) (some (1, 4, 5)) (some (1, 4, 5))
    (.terminal (some (1, 4, 5)) (some (1, 4, 0)) (some (1, 4, 5)))))))))))))))))))))))))))

theorem excluded24_0 : ExcludedOn (model24.B 0 ++ [step24.q]) 9000000000000 (model24.caps 0)
    (model24.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_1 : ExcludedOn (model24.B 1 ++ [step24.q]) 9000000000000 (model24.caps 1)
    (model24.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_2 : ExcludedOn (model24.B 2 ++ [step24.q]) 9000000000000 (model24.caps 2)
    (model24.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_4 : ExcludedOn (model24.B 4 ++ [step24.q]) 9000000000000 (model24.caps 4)
    (model24.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5184000000000], [1245000000000]) (some (6, 0,
      2)) (some (6, 1, 2)) (.next ([2184000000000], [936000000000]) (some (6, 1, 2)) (some (6, 1,
      2)) (.next ([5184000000000], [2745000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
      ([1455000000000], [795000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([3870000000000],
      [2250000000000]) (some (6, 1, 2)) (some (6, 1, 3)) fan24Owner4Part0)))))) (den :=
      9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_5 : ExcludedOn (model24.B 5 ++ [step24.q]) 9000000000000 (model24.caps 5)
    (model24.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_6 : ExcludedOn (model24.B 6 ++ [step24.q]) 9000000000000 (model24.caps 6)
    (model24.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_7 : ExcludedOn (model24.B 7 ++ [step24.q]) 9000000000000 (model24.caps 7)
    (model24.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_8 : ExcludedOn (model24.B 8 ++ [step24.q]) 9000000000000 (model24.caps 8)
    (model24.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4566000000000], [5184000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([1125000000000], [4365000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([306000000000], [4260000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([201000000000], [5184000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [4365000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.next ([-5184000000000], [9750000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-4365000000000], [5490000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-4260000000000], [4566000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-5184000000000], [5385000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_9 : ExcludedOn (model24.B 9 ++ [step24.q]) 9000000000000 (model24.caps 9)
    (model24.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded24_1
    · exact excluded24_2
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 2 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_1 : ExcludedOn (model25.B 1 ++ [step25.q]) 9000000000000 (model25.caps 1)
    (model25.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_2 : ExcludedOn (model25.B 2 ++ [step25.q]) 9000000000000 (model25.caps 2)
    (model25.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1965000000000], [30000000000]) (some (0, 1, 4))
      (some (6, 2, 4)) (.next ([1710000000000], [285000000000]) (some (6, 2, 4)) (some (6, 2, 4))
      (.next ([5130000000000, 9000000000000], [990000000000, -9000000000000]) (some (6, 2, 4)) (some
      (6, 2, 4)) (.next ([3165000000000], [705000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
      ([4875000000000, 9000000000000], [1245000000000, -9000000000000]) (some (6, 2, 4)) (some (6,
      2, 4)) (.next ([3165000000000, 9000000000000], [960000000000, -9000000000000]) (some (6, 2,
      4)) (some (6, 2, 4)) (.next ([3165000000000], [960000000000]) (some (6, 2, 4)) (some (6, 2,
      4)) (.next ([3840000000000], [1335000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
      ([2880000000000, 9000000000000], [2955000000000, 0]) (some (6, 2, 4)) (some (6, 2, 4))
      fan25Owner2Part0)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_4 : ExcludedOn (model25.B 4 ++ [step25.q]) 9000000000000 (model25.caps 4)
    (model25.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_5 : ExcludedOn (model25.B 5 ++ [step25.q]) 9000000000000 (model25.caps 5)
    (model25.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_6 : ExcludedOn (model25.B 6 ++ [step25.q]) 9000000000000 (model25.caps 6)
    (model25.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_7 : ExcludedOn (model25.B 7 ++ [step25.q]) 9000000000000 (model25.caps 7)
    (model25.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_8 : ExcludedOn (model25.B 8 ++ [step25.q]) 9000000000000 (model25.caps 8)
    (model25.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_9 : ExcludedOn (model25.B 9 ++ [step25.q]) 9000000000000 (model25.caps 9)
    (model25.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded25_4
    · exact excluded25_5
    · exact excluded25_6
    · exact excluded25_7
    · exact excluded25_8
    · exact excluded25_9
theorem next25 : model25.insert step25 = model26 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded26_0 : ExcludedOn (model26.B 0 ++ [step26.q]) 9000000000000 (model26.caps 0)
    (model26.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_1 : ExcludedOn (model26.B 1 ++ [step26.q]) 9000000000000 (model26.caps 1)
    (model26.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_2 : ExcludedOn (model26.B 2 ++ [step26.q]) 9000000000000 (model26.caps 2)
    (model26.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1965000000000], [30000000000]) (some (0, 1, 4))
      (some (0, 2, 4)) (.next ([5184000000000], [441000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([1710000000000], [285000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([5130000000000, 9000000000000], [990000000000, -9000000000000]) (some (0, 2, 4)) (some (0, 2,
      4)) (.next ([2229000000000], [441000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([3165000000000], [705000000000]) (some (0, 2, 4)) (some (6, 2, 4)) (.next ([4875000000000,
      9000000000000], [1245000000000, -9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
      ([3165000000000, 9000000000000], [960000000000, -9000000000000]) (some (6, 2, 4)) (some (6, 2,
      4)) (.next ([3165000000000], [960000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
      ([3399000000000], [1500000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([2880000000000,
      9000000000000], [2955000000000, 0]) (some (6, 2, 4)) (some (6, 2, 4))
      fan26Owner2Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded26_4 : ExcludedOn (model26.B 4 ++ [step26.q]) 9000000000000 (model26.caps 4)
    (model26.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_5 : ExcludedOn (model26.B 5 ++ [step26.q]) 9000000000000 (model26.caps 5)
    (model26.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_6 : ExcludedOn (model26.B 6 ++ [step26.q]) 9000000000000 (model26.caps 6)
    (model26.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_7 : ExcludedOn (model26.B 7 ++ [step26.q]) 9000000000000 (model26.caps 7)
    (model26.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_8 : ExcludedOn (model26.B 8 ++ [step26.q]) 9000000000000 (model26.caps 8)
    (model26.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_9 : ExcludedOn (model26.B 9 ++ [step26.q]) 9000000000000 (model26.caps 9)
    (model26.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded26_1
    · exact excluded26_2
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 1 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_1 : ExcludedOn (model27.B 1 ++ [step27.q]) 9000000000000 (model27.caps 1)
    (model27.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_2 : ExcludedOn (model27.B 2 ++ [step27.q]) 9000000000000 (model27.caps 2)
    (model27.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_3 : ExcludedOn (model27.B 3 ++ [step27.q]) 9000000000000 (model27.caps 3)
    (model27.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6165000000000], [195000000000]) (some (4, 1, 2))
      (some (6, 1, 2)) (.next ([2685000000000, 9000000000000], [195000000000]) (some (6, 1, 2))
      (some (6, 1, 2)) (.next ([3816000000000], [750000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([3621000000000], [945000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
      ([3816000000000], [2439000000000, 9000000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
      ([3375000000000], [2349000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([3540000000000],
      [2625000000000]) (some (6, 1, 2)) (some (6, 1, 3)) fan27Owner3Part0)))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_4 : ExcludedOn (model27.B 4 ++ [step27.q]) 9000000000000 (model27.caps 4)
    (model27.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_5 : ExcludedOn (model27.B 5 ++ [step27.q]) 9000000000000 (model27.caps 5)
    (model27.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_6 : ExcludedOn (model27.B 6 ++ [step27.q]) 9000000000000 (model27.caps 6)
    (model27.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_7 : ExcludedOn (model27.B 7 ++ [step27.q]) 9000000000000 (model27.caps 7)
    (model27.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_9 : ExcludedOn (model27.B 9 ++ [step27.q]) 9000000000000 (model27.caps 9)
    (model27.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded27_4
    · exact excluded27_5
    · exact excluded27_6
    · exact excluded27_7
    · exact (hj rfl).elim
    · exact excluded27_9
theorem next27 : model27.insert step27 = model28 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded28_0 : ExcludedOn (model28.B 0 ++ [step28.q]) 9000000000000 (model28.caps 0)
    (model28.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_1 : ExcludedOn (model28.B 1 ++ [step28.q]) 9000000000000 (model28.caps 1)
    (model28.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_2 : ExcludedOn (model28.B 2 ++ [step28.q]) 9000000000000 (model28.caps 2)
    (model28.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_4 : ExcludedOn (model28.B 4 ++ [step28.q]) 9000000000000 (model28.caps 4)
    (model28.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4620000000000], [45000000000]) (some (6, 0, 2))
      (some (6, 1, 2)) (.next ([5184000000000], [1245000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([1686000000000], [564000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      fan28Owner4Part0))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded28_5 : ExcludedOn (model28.B 5 ++ [step28.q]) 9000000000000 (model28.caps 5)
    (model28.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_6 : ExcludedOn (model28.B 6 ++ [step28.q]) 9000000000000 (model28.caps 6)
    (model28.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_7 : ExcludedOn (model28.B 7 ++ [step28.q]) 9000000000000 (model28.caps 7)
    (model28.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_8 : ExcludedOn (model28.B 8 ++ [step28.q]) 9000000000000 (model28.caps 8)
    (model28.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4185000000000], [195000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([4440000000000], [4365000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([4380000000000], [4620000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([15000000000], [4620000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [4365000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.next ([-195000000000], [4380000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-4365000000000], [8805000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-4620000000000], [9000000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-4620000000000], [4635000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded28_9 : ExcludedOn (model28.B 9 ++ [step28.q]) 9000000000000 (model28.caps 9)
    (model28.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked28 : StepValid model28 9000000000000 step28 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded28_0
    · exact excluded28_1
    · exact excluded28_2
    · exact (hj rfl).elim
    · exact excluded28_4
    · exact excluded28_5
    · exact excluded28_6
    · exact excluded28_7
    · exact excluded28_8
    · exact excluded28_9
theorem next28 : model28.insert step28 = model29 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded29_0 : ExcludedOn (model29.B 0 ++ [step29.q]) 9000000000000 (model29.caps 0)
    (model29.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_1 : ExcludedOn (model29.B 1 ++ [step29.q]) 9000000000000 (model29.caps 1)
    (model29.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_3 : ExcludedOn (model29.B 3 ++ [step29.q]) 9000000000000 (model29.caps 3)
    (model29.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6375000000000], [540000000000]) (some (3, 0, 5))
      (some (4, 0, 5)) fan29Owner3Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded29_4 : ExcludedOn (model29.B 4 ++ [step29.q]) 9000000000000 (model29.caps 4)
    (model29.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_5 : ExcludedOn (model29.B 5 ++ [step29.q]) 9000000000000 (model29.caps 5)
    (model29.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_6 : ExcludedOn (model29.B 6 ++ [step29.q]) 9000000000000 (model29.caps 6)
    (model29.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_7 : ExcludedOn (model29.B 7 ++ [step29.q]) 9000000000000 (model29.caps 7)
    (model29.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_8 : ExcludedOn (model29.B 8 ++ [step29.q]) 9000000000000 (model29.caps 8)
    (model29.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_9 : ExcludedOn (model29.B 9 ++ [step29.q]) 9000000000000 (model29.caps 9)
    (model29.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked29 : StepValid model29 9000000000000 step29 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded29_0
    · exact excluded29_1
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_2 : ExcludedOn (model30.B 2 ++ [step30.q]) 9000000000000 (model30.caps 2)
    (model30.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3510000000000], [330000000000]) (some (0, 1, 4))
      (some (6, 1, 4)) (.next ([5505000000000, 9000000000000], [960000000000, -9000000000000]) (some
      (6, 1, 4)) (some (6, 1, 4)) (.next ([4875000000000, 9000000000000], [1245000000000,
      -9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3165000000000, 9000000000000],
      [960000000000, -9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3165000000000],
      [960000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3840000000000], [1215000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([2880000000000, 9000000000000], [2955000000000, 0])
      (some (6, 1, 4)) (some (6, 1, 4)) fan30Owner2Part0)))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded30_3 : ExcludedOn (model30.B 3 ++ [step30.q]) 9000000000000 (model30.caps 3)
    (model30.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([285000000000], [156000000000]) (some (3, 0, 1))
      (some (4, 0, 1)) (.next ([3660000000000], [2505000000000]) (some (4, 0, 1)) (some (4, 0, 1))
      (.next ([3375000000000], [2349000000000]) (some (4, 0, 1)) (some (4, 0, 5)) (.next
      ([3540000000000], [2625000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([3816000000000],
      [3939000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([3660000000000], [4380000000000])
      (some (4, 0, 5)) (some (4, 0, 5)) (.next ([3540000000000], [4380000000000]) (some (4, 0, 5))
      (some (4, 0, 5)) (.next ([165000000000], [276000000000]) (some (4, 0, 5)) (some (4, 0, 5))
      (.next ([1785000000000], [4380000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
      ([441000000000], [3375000000000]) (some (4, 0, 5)) (some (4, 1, 5)) (.next ([0],
      [4380000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([-156000000000], [441000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2505000000000], [6165000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([-2349000000000], [5724000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([-2625000000000], [6165000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-3939000000000], [7755000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-4380000000000], [8040000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-4380000000000], [7920000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-276000000000],
      [441000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4380000000000], [6165000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3375000000000], [3816000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.terminal (some (0, 1, 5)) (some (0, 1, 3)) (some (0, 1,
      5))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded30_4 : ExcludedOn (model30.B 4 ++ [step30.q]) 9000000000000 (model30.caps 4)
    (model30.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_5 : ExcludedOn (model30.B 5 ++ [step30.q]) 9000000000000 (model30.caps 5)
    (model30.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_6 : ExcludedOn (model30.B 6 ++ [step30.q]) 9000000000000 (model30.caps 6)
    (model30.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_7 : ExcludedOn (model30.B 7 ++ [step30.q]) 9000000000000 (model30.caps 7)
    (model30.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_8 : ExcludedOn (model30.B 8 ++ [step30.q]) 9000000000000 (model30.caps 8)
    (model30.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_9 : ExcludedOn (model30.B 9 ++ [step30.q]) 9000000000000 (model30.caps 9)
    (model30.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

end Sext320000330000
end ConwaySoifer.Simplified.Certificates
