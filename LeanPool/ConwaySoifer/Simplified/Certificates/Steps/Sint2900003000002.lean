/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint290000300000
import Mathlib.Tactic.FinCases

/-!
# Sint 290000 300000 2

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
namespace Sint290000300000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan16Owner4Part0 : FanWitness := (.next ([-1680000000000], [6345000000000]) (some (0, 9, 6))
    (some (0, 9, 6)) (.next ([-1095000000000], [3735000000000]) (some (0, 9, 6)) (some (0, 9, 6))
    (.next ([-1185000000000], [3915000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next
    ([-405000000000], [1305000000000]) (some (0, 9, 6)) (some (0, 9, 7)) (.next ([-1245000000000],
    [3720000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-855000000000], [2520000000000])
    (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-390000000000], [1140000000000]) (some (0, 9, 7))
    (some (0, 9, 7)) (.next ([-1890000000000], [5370000000000]) (some (0, 9, 7)) (some (0, 9, 7))
    (.next ([-300000000000], [780000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next
    ([-2055000000000, 9000000000000], [4665000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next
    ([-2475000000000], [5100000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-2640000000000],
    [5250000000000, 9000000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-2640000000000],
    [5250000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-3000000000000], [5520000000000])
    (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-2640000000000], [4665000000000]) (some (0, 9, 7))
    (some (0, 9, 7)) (.next ([-1335000000000], [2220000000000]) (some (0, 9, 7)) (some (0, 9, 7))
    (.next ([-5595000000000], [9075000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next
    ([-3780000000000], [6000000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-6345000000000],
    [8955000000000, 9000000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-2730000000000],
    [3480000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-4350000000000], [5355000000000])
    (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-4500000000000], [5340000000000]) (some (0, 9, 7))
    (some (0, 9, 7)) (.next ([-4770000000000], [5250000000000]) (some (0, 9, 7)) (some (0, 9, 7))
    (.next ([-5100000000000], [5235000000000, 9000000000000]) (some (0, 9, 7)) (some (0, 9, 7))
    (.terminal (some (0, 9, 7)) (some (0, 9, 7)) (some (0, 9, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan16Owner4Part1 : FanWitness := (.next ([2025000000000], [2640000000000]) (some (8, 9, 5))
    (some (8, 9, 5)) (.next ([885000000000], [1335000000000]) (some (8, 9, 5)) (some (8, 9, 5))
    (.next ([3480000000000], [5595000000000]) (some (8, 9, 5)) (some (8, 9, 6)) (.next
    ([2220000000000], [3780000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([2610000000000,
    9000000000000], [6345000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([750000000000],
    [2730000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([1005000000000], [4350000000000])
    (some (8, 9, 6)) (some (8, 9, 6)) (.next ([840000000000], [4500000000000]) (some (8, 9, 6))
    (some (8, 9, 6)) (.next ([480000000000], [4770000000000]) (some (8, 9, 6)) (some (8, 9, 6))
    (.next ([135000000000, 9000000000000], [5100000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
    ([-30000000000, 9000000000000], [5250000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
    ([-15000000000], [2475000000000]) (some (8, 9, 6)) (some (0, 9, 6)) (.next ([-30000000000],
    [2640000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([-120000000000], [3000000000000])
    (some (0, 9, 6)) (some (0, 9, 6)) (.next ([-300000000000], [5250000000000]) (some (0, 9, 6))
    (some (0, 9, 6)) (.next ([-345000000000], [4125000000000]) (some (0, 9, 6)) (some (0, 9, 6))
    (.next ([-15000000000], [165000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next
    ([-420000000000], [3780000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([-435000000000],
    [2625000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([-1170000000000, 9000000000000],
    [6000000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([-105000000000], [525000000000])
    (some (0, 9, 6)) (some (0, 9, 6)) (.next ([-825000000000], [3825000000000]) (some (0, 9, 6))
    (some (0, 9, 6)) (.next ([-585000000000], [2610000000000]) (some (0, 9, 6)) (some (0, 9, 6))
    (.next ([-90000000000], [360000000000]) (some (0, 9, 6)) (some (0, 9, 6))
    fan16Owner4Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan16Owner4Part2 : FanWitness := (.next ([4950000000000], [300000000000]) (some (7, 9, 9)) (some
    (7, 9, 9)) (.next ([3780000000000], [345000000000]) (some (7, 9, 9)) (some (7, 9, 9)) (.next
    ([150000000000], [15000000000]) (some (7, 9, 5)) (some (7, 9, 5)) (.next ([3360000000000],
    [420000000000]) (some (7, 9, 5)) (some (8, 9, 5)) (.next ([2190000000000], [435000000000]) (some
    (8, 9, 5)) (some (8, 9, 5)) (.next ([4830000000000, 9000000000000], [1170000000000,
    -9000000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([420000000000], [105000000000]) (some
    (8, 9, 5)) (some (8, 9, 5)) (.next ([3000000000000], [825000000000]) (some (8, 9, 5)) (some (8,
    9, 5)) (.next ([2025000000000], [585000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next
    ([270000000000], [90000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([4665000000000],
    [1680000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([2640000000000], [1095000000000])
    (some (8, 9, 5)) (some (8, 9, 5)) (.next ([2730000000000], [1185000000000]) (some (8, 9, 5))
    (some (8, 9, 5)) (.next ([900000000000], [405000000000]) (some (8, 9, 5)) (some (8, 9, 5))
    (.next ([2475000000000], [1245000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next
    ([1665000000000], [855000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([750000000000],
    [390000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([3480000000000], [1890000000000])
    (some (8, 9, 5)) (some (8, 9, 5)) (.next ([480000000000], [300000000000]) (some (8, 9, 5)) (some
    (8, 9, 5)) (.next ([2610000000000, 9000000000000], [2055000000000, -9000000000000]) (some (8, 9,
    5)) (some (8, 9, 5)) (.next ([2625000000000], [2475000000000]) (some (8, 9, 5)) (some (8, 9, 5))
    (.next ([2610000000000, 9000000000000], [2640000000000]) (some (8, 9, 5)) (some (8, 9, 5))
    (.next ([2610000000000], [2640000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next
    ([2520000000000], [3000000000000]) (some (8, 9, 5)) (some (8, 9, 5))
    fan16Owner4Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan17Owner0Part0 : FanWitness := (.next ([2895000000000], [6927000000000]) (some (5, 6, 4))
    (some (5, 6, 4)) (.next ([1575000000000], [4695000000000]) (some (5, 6, 4)) (some (6, 6, 4))
    (.next ([1425000000000], [5625000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next
    ([825000000000], [6000000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next ([261000000000,
    -2100000000000], [6093000000000, 4200000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next
    ([-339000000000, -2100000000000], [6468000000000, 4200000000000]) (some (6, 6, 4)) (some (6, 6,
    4)) (.next ([-141000000000, 2100000000000], [1914000000000, 2100000000000]) (some (6, 6, 4))
    (some (6, 6, 4)) (.next ([-435000000000], [5430000000000]) (some (6, 6, 4)) (some (6, 6, 4))
    (.next ([-195000000000], [2055000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next
    ([-459000000000, 4200000000000], [3693000000000, -2100000000000]) (some (6, 6, 4)) (some (6, 6,
    4)) (.next ([-1035000000000], [5805000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-1122000000000], [5052000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-927000000000],
    [2997000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-225000000000], [600000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-663000000000, -4200000000000], [1359000000000,
    2100000000000]) (some (6, 2, 4)) (some (6, 2, 5)) (.next ([-750000000000], [1305000000000])
    (some (6, 2, 5)) (some (6, 3, 5)) (.next ([-2232000000000], [3552000000000]) (some (6, 3, 5))
    (some (6, 3, 5)) (.next ([-6552000000000], [10047000000000]) (some (6, 3, 5)) (some (6, 3, 5))
    (.next ([-4320000000000], [6495000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-6927000000000], [9822000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-4695000000000],
    [6270000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-5625000000000], [7050000000000])
    (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-6000000000000], [6825000000000]) (some (6, 3, 5))
    (some (6, 3, 5)) (.next ([-6093000000000, -4200000000000], [6354000000000, 2100000000000]) (some
    (6, 3, 5)) (some (6, 3, 5)) (.terminal (some (6, 3, 5)) (some (6, 3, 5)) (some (6, 3,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part0 : FanWitness := (.next ([1140000000000], [3915000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([1425000000000], [5625000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([585000000000], [3165000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([825000000000], [6000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([261000000000,
    -2100000000000], [6093000000000, 4200000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-339000000000, -2100000000000], [6468000000000, 4200000000000]) (some (0, 6, 4)) (some (0, 6,
    4)) (.next ([-141000000000, 2100000000000], [1914000000000, 2100000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-435000000000], [5430000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-195000000000], [2055000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-1035000000000], [5805000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1740000000000],
    [9375000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2340000000000], [9750000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1305000000000], [3945000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-225000000000], [600000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-663000000000, -4200000000000], [1359000000000, 2100000000000]) (some (0, 6, 4)) (some
    (0, 6, 5)) (.next ([-750000000000], [1305000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-2001000000000, 2100000000000], [3282000000000, -4200000000000]) (some (0, 6, 5)) (some (1, 6,
    5)) (.next ([-4320000000000], [6495000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next
    ([-4695000000000], [6270000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-3915000000000],
    [5055000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-5625000000000], [7050000000000])
    (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-3165000000000], [3750000000000]) (some (1, 6, 5))
    (some (1, 6, 5)) (.next ([-6000000000000], [6825000000000]) (some (1, 6, 5)) (some (6, 6, 5))
    (.next ([-6093000000000, -4200000000000], [6354000000000, 2100000000000]) (some (6, 6, 5)) (some
    (6, 6, 5)) (.terminal (some (6, 6, 5)) (some (6, 6, 5)) (some (6, 6,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner0Part0 : FanWitness := (.next ([1125000000000], [3915000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([1425000000000], [5625000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([570000000000], [3165000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([825000000000], [6000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([261000000000,
    -2100000000000], [6093000000000, 4200000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-339000000000, -2100000000000], [6468000000000, 4200000000000]) (some (0, 6, 4)) (some (0, 6,
    4)) (.next ([-141000000000, 2100000000000], [1914000000000, 2100000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-435000000000], [5430000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-195000000000], [2055000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-1035000000000], [5805000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1740000000000],
    [9360000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2340000000000], [9735000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1305000000000], [3930000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-225000000000], [600000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-663000000000, -4200000000000], [1359000000000, 2100000000000]) (some (0, 6, 4)) (some
    (0, 6, 5)) (.next ([-750000000000], [1305000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-2001000000000, 2100000000000], [3267000000000, -4200000000000]) (some (0, 6, 5)) (some (1, 6,
    5)) (.next ([-4320000000000], [6495000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next
    ([-4695000000000], [6270000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-3915000000000],
    [5040000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-5625000000000], [7050000000000])
    (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-3165000000000], [3735000000000]) (some (1, 6, 5))
    (some (1, 6, 5)) (.next ([-6000000000000], [6825000000000]) (some (1, 6, 5)) (some (6, 6, 5))
    (.next ([-6093000000000, -4200000000000], [6354000000000, 2100000000000]) (some (6, 6, 5)) (some
    (6, 6, 5)) (.terminal (some (6, 6, 5)) (some (6, 6, 5)) (some (6, 6,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part0 : FanWitness := (.next ([2175000000000], [4320000000000]) (some (5, 6, 4))
    (some (5, 6, 4)) (.next ([1575000000000], [4695000000000]) (some (5, 6, 4)) (some (5, 6, 4))
    (.next ([1425000000000], [5625000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([825000000000], [6000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([339000000000,
    -2100000000000], [3141000000000, -2100000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([261000000000, -2100000000000], [6093000000000, 4200000000000]) (some (0, 6, 4)) (some (0, 6,
    4)) (.next ([-339000000000, -2100000000000], [6468000000000, 4200000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-141000000000, 2100000000000], [1914000000000, 2100000000000]) (some
    (0, 6, 4)) (some (0, 6, 4)) (.next ([-435000000000], [5430000000000]) (some (0, 6, 4)) (some (0,
    6, 4)) (.next ([-357000000000], [4305000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-195000000000], [2055000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1035000000000],
    [5805000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2880000000000], [9573000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3480000000000], [9948000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-225000000000], [600000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-663000000000, -4200000000000], [1359000000000, 2100000000000]) (some (0, 6, 4)) (some
    (0, 6, 5)) (.next ([-750000000000], [1305000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-2445000000000], [4143000000000]) (some (0, 6, 5)) (some (1, 6, 5)) (.next ([-4320000000000],
    [6495000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-4695000000000], [6270000000000])
    (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-5625000000000], [7050000000000]) (some (1, 6, 5))
    (some (1, 6, 5)) (.next ([-6000000000000], [6825000000000]) (some (1, 6, 5)) (some (1, 6, 5))
    (.next ([-3141000000000, 2100000000000], [3480000000000, -4200000000000]) (some (1, 6, 5)) (some
    (1, 6, 5)) (.next ([-6093000000000, -4200000000000], [6354000000000, 2100000000000]) (some (1,
    6, 5)) (some (1, 6, 5)) (.terminal (some (1, 6, 5)) (some (1, 6, 5)) (some (1, 6,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner4Part0 : FanWitness := (.next ([-2475000000000], [7080000000000]) (some (10, 4, 8))
    (some (10, 4, 8)) (.next ([-1890000000000], [5370000000000]) (some (10, 4, 8)) (some (10, 4, 8))
    (.next ([-2640000000000], [7230000000000]) (some (10, 4, 8)) (some (10, 4, 8)) (.next
    ([-300000000000], [780000000000]) (some (10, 4, 8)) (some (10, 4, 8)) (.next ([-3000000000000],
    [7500000000000]) (some (10, 4, 8)) (some (10, 5, 8)) (.next ([-948000000000], [2223000000000])
    (some (10, 5, 8)) (some (10, 5, 8)) (.next ([-933000000000], [2058000000000]) (some (10, 5, 8))
    (some (10, 5, 8)) (.next ([-3780000000000], [7980000000000]) (some (10, 5, 8)) (some (10, 5, 8))
    (.next ([-2475000000000], [5100000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next
    ([-843000000000], [1698000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next ([-2640000000000],
    [5250000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next ([-3000000000000], [5520000000000])
    (some (10, 5, 8)) (some (10, 5, 8)) (.next ([-4698000000000], [8355000000000]) (some (10, 5, 8))
    (some (10, 5, 8)) (.next ([-2640000000000], [4665000000000]) (some (10, 5, 8)) (some (10, 5, 8))
    (.next ([-543000000000], [918000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next
    ([-1335000000000], [2220000000000]) (some (10, 5, 8)) (some (10, 6, 8)) (.next
    ([-3780000000000], [6000000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next
    ([-4665000000000], [6645000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next
    ([-4698000000000], [6375000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next
    ([-2730000000000], [3480000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next
    ([-4350000000000], [5355000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next
    ([-4500000000000], [5340000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next
    ([-4770000000000], [5250000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next
    ([-5100000000000], [5235000000000, 9000000000000]) (some (10, 6, 8)) (some (10, 6, 8))
    (.terminal (some (10, 6, 8)) (some (0, 6, 8)) (some (10, 6, 8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner4Part1 : FanWitness := (.next ([840000000000], [4500000000000]) (some (10, 1, 6))
    (some (10, 1, 6)) (.next ([480000000000], [4770000000000]) (some (10, 1, 6)) (some (10, 1, 6))
    (.next ([135000000000, 9000000000000], [5100000000000]) (some (10, 1, 6)) (some (10, 1, 6))
    (.next ([-30000000000, 9000000000000], [5250000000000]) (some (10, 1, 6)) (some (10, 1, 6))
    (.next ([-15000000000], [2475000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next
    ([-30000000000], [2640000000000]) (some (10, 1, 6)) (some (10, 2, 6)) (.next ([-33000000000],
    [1710000000000]) (some (10, 2, 6)) (some (10, 2, 6)) (.next ([-120000000000], [3000000000000])
    (some (10, 2, 6)) (some (10, 2, 7)) (.next ([-300000000000], [5250000000000]) (some (10, 2, 7))
    (some (10, 2, 7)) (.next ([-15000000000], [165000000000]) (some (10, 2, 7)) (some (10, 2, 7))
    (.next ([-420000000000], [3780000000000]) (some (10, 2, 7)) (some (10, 3, 7)) (.next
    ([-435000000000], [2625000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-1170000000000,
    9000000000000], [6000000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-105000000000],
    [525000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-963000000000], [4698000000000])
    (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-750000000000], [3480000000000]) (some (10, 3, 7))
    (some (10, 3, 7)) (.next ([-1218000000000], [5625000000000]) (some (10, 3, 7)) (some (10, 3, 7))
    (.next ([-585000000000], [2610000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next
    ([-90000000000], [360000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-1185000000000],
    [3915000000000]) (some (10, 3, 7)) (some (10, 4, 7)) (.next ([-405000000000], [1305000000000])
    (some (10, 4, 7)) (some (10, 4, 8)) (.next ([-2088000000000, 9000000000000], [6375000000000])
    (some (10, 4, 8)) (some (10, 4, 8)) (.next ([-855000000000], [2520000000000]) (some (10, 4, 8))
    (some (10, 4, 8)) (.next ([-390000000000], [1140000000000]) (some (10, 4, 8)) (some (10, 4, 8))
    fan21Owner4Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner4Part2 : FanWitness := (.next ([4287000000000, 9000000000000], [2088000000000,
    -9000000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next ([1665000000000], [855000000000])
    (some (10, 1, 6)) (some (10, 1, 6)) (.next ([750000000000], [390000000000]) (some (10, 1, 6))
    (some (10, 1, 6)) (.next ([4605000000000], [2475000000000]) (some (10, 1, 6)) (some (10, 1, 6))
    (.next ([3480000000000], [1890000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next
    ([4590000000000], [2640000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next ([480000000000],
    [300000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next ([4500000000000], [3000000000000])
    (some (10, 1, 6)) (some (10, 1, 6)) (.next ([1275000000000], [948000000000]) (some (10, 1, 6))
    (some (10, 1, 6)) (.next ([1125000000000], [933000000000]) (some (10, 1, 6)) (some (10, 1, 6))
    (.next ([4200000000000], [3780000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next
    ([2625000000000], [2475000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next ([855000000000],
    [843000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next ([2610000000000], [2640000000000])
    (some (10, 1, 6)) (some (10, 1, 6)) (.next ([2520000000000], [3000000000000]) (some (10, 1, 6))
    (some (10, 1, 6)) (.next ([3657000000000], [4698000000000]) (some (10, 1, 6)) (some (10, 1, 6))
    (.next ([2025000000000], [2640000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next
    ([375000000000], [543000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next ([885000000000],
    [1335000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next ([2220000000000], [3780000000000])
    (some (10, 1, 6)) (some (10, 1, 6)) (.next ([1980000000000], [4665000000000]) (some (10, 1, 6))
    (some (10, 1, 6)) (.next ([1677000000000], [4698000000000]) (some (10, 1, 6)) (some (10, 1, 6))
    (.next ([750000000000], [2730000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next
    ([1005000000000], [4350000000000]) (some (10, 1, 6)) (some (10, 1, 6))
    fan21Owner4Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner6Part0 : FanWitness := (.next ([4500000000000], [1890000000000]) (some (5, 6, 3))
    (some (5, 6, 3)) (.next ([2610000000000, 9000000000000], [2610000000000, 9000000000000]) (some
    (5, 6, 3)) (some (5, 6, 3)) (.next ([1515000000000, 0], [2265000000000, -9000000000000]) (some
    (5, 6, 3)) (some (5, 6, 3)) (.next ([1662000000000, 9000000000000], [2640000000000,
    -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1692000000000, -9000000000000],
    [3558000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1905000000000,
    -9000000000000], [4485000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([1890000000000, -9000000000000], [4500000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1,
    3)) (.next ([1515000000000], [4875000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([213000000000], [927000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([198000000000],
    [942000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([0], [15000000000]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([-1095000000000, -9000000000000], [7485000000000, 9000000000000]) (some
    (0, 1, 3)) (some (6, 2, 3)) (.next ([-948000000000], [5250000000000]) (some (6, 2, 3)) (some (6,
    2, 3)) (.next ([-1875000000000], [6390000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next
    ([-1890000000000], [6390000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next ([-2610000000000,
    -9000000000000], [5220000000000, 18000000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next
    ([-2265000000000, 9000000000000], [3780000000000, -9000000000000]) (some (6, 2, 3)) (some (6, 2,
    3)) (.next ([-2640000000000, 9000000000000], [4302000000000]) (some (6, 2, 3)) (some (6, 2, 3))
    (.next ([-3558000000000, -9000000000000], [5250000000000]) (some (6, 2, 3)) (some (6, 2, 3))
    (.next ([-4485000000000, -9000000000000], [6390000000000]) (some (6, 2, 3)) (some (6, 2, 4))
    (.next ([-4500000000000, -9000000000000], [6390000000000]) (some (6, 2, 4)) (some (6, 2, 4))
    (.next ([-4875000000000], [6390000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-927000000000], [1140000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-942000000000],
    [1140000000000]) (some (6, 2, 4)) (some (6, 2, 5)) (.terminal (some (6, 2, 5)) (some (6, 2, 5))
    (some (6, 2, 5)))))))))))))))))))))))))))

theorem excluded16_0 : ExcludedOn (model16.B 0 ++ [step16.q]) 9000000000000 (model16.caps 0)
    (model16.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_4 : ExcludedOn (model16.B 4 ++ [step16.q]) 9000000000000 (model16.caps 4)
    (model16.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2460000000000], [15000000000]) (some (7, 0, 9))
      (some (7, 9, 9)) (.next ([2610000000000], [30000000000]) (some (7, 9, 9)) (some (7, 9, 9))
      (.next ([2880000000000], [120000000000]) (some (7, 9, 9)) (some (7, 9, 9))
      fan16Owner4Part2)))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_6 : ExcludedOn (model16.B 6 ++ [step16.q]) 9000000000000 (model16.caps 6)
    (model16.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_7 : ExcludedOn (model16.B 7 ++ [step16.q]) 9000000000000 (model16.caps 7)
    (model16.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_8 : ExcludedOn (model16.B 8 ++ [step16.q]) 9000000000000 (model16.caps 8)
    (model16.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_9 : ExcludedOn (model16.B 9 ++ [step16.q]) 9000000000000 (model16.caps 9)
    (model16.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded16_6
    · exact excluded16_7
    · exact excluded16_8
    · exact excluded16_9
theorem next16 : model16.insert step16 = model17 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded17_0 : ExcludedOn (model17.B 0 ++ [step17.q]) 9000000000000 (model17.caps 0)
    (model17.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6129000000000, 2100000000000], [339000000000,
      2100000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([1773000000000, 4200000000000],
      [141000000000, -2100000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([4995000000000],
      [435000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([1860000000000], [195000000000])
      (some (5, 6, 3)) (some (5, 6, 4)) (.next ([3234000000000, 2100000000000], [459000000000,
      -4200000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([4770000000000], [1035000000000])
      (some (5, 6, 4)) (some (5, 6, 4)) (.next ([3930000000000], [1122000000000]) (some (5, 6, 4))
      (some (5, 6, 4)) (.next ([2070000000000], [927000000000]) (some (5, 6, 4)) (some (5, 6, 4))
      (.next ([375000000000], [225000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
      ([696000000000, -2100000000000], [663000000000, 4200000000000]) (some (5, 6, 4)) (some (5, 6,
      4)) (.next ([555000000000], [750000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
      ([1320000000000], [2232000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([3495000000000],
      [6552000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([2175000000000], [4320000000000])
      (some (5, 6, 4)) (some (5, 6, 4)) fan17Owner0Part0)))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_5 : ExcludedOn (model17.B 5 ++ [step17.q]) 9000000000000 (model17.caps 5)
    (model17.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4698000000000], [2625000000000]) (some (4, 0,
      2)) (some (4, 1, 2)) (.next ([3795000000000, -9000000000000], [2610000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2655000000000, 0], [2610000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 3)) (.next ([2655000000000], [3750000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([918000000000], [1707000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([2088000000000, -9000000000000], [5235000000000, 9000000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([30000000000], [4668000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([0], [2655000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2625000000000],
      [7323000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-2610000000000, -9000000000000],
      [6405000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2610000000000, -9000000000000],
      [5265000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3750000000000],
      [6405000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1707000000000], [2625000000000])
      (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-5235000000000, -9000000000000], [7323000000000])
      (some (0, 2, 3)) (some (0, 2, 4)) (.next ([-4668000000000], [4698000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2,
      4))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded17_6 : ExcludedOn (model17.B 6 ++ [step17.q]) 9000000000000 (model17.caps 6)
    (model17.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_7 : ExcludedOn (model17.B 7 ++ [step17.q]) 9000000000000 (model17.caps 7)
    (model17.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_8 : ExcludedOn (model17.B 8 ++ [step17.q]) 9000000000000 (model17.caps 8)
    (model17.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6129000000000, 2100000000000], [339000000000,
      2100000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next ([1773000000000, 4200000000000],
      [141000000000, -2100000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next ([4995000000000],
      [435000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next ([1860000000000], [195000000000])
      (some (5, 6, 6)) (some (5, 6, 6)) (.next ([4770000000000], [1035000000000]) (some (5, 6, 6))
      (some (5, 6, 6)) (.next ([7635000000000], [1740000000000]) (some (5, 6, 6)) (some (5, 6, 6))
      (.next ([7410000000000], [2340000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
      ([2640000000000], [1305000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([375000000000],
      [225000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([696000000000, -2100000000000],
      [663000000000, 4200000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([555000000000],
      [750000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([1281000000000, -2100000000000],
      [2001000000000, -2100000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([2175000000000],
      [4320000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([1575000000000], [4695000000000])
      (some (5, 6, 4)) (some (5, 6, 4)) fan18Owner0Part0)))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_4 : ExcludedOn (model18.B 4 ++ [step18.q]) 9000000000000 (model18.caps 4)
    (model18.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_5 : ExcludedOn (model18.B 5 ++ [step18.q]) 9000000000000 (model18.caps 5)
    (model18.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4500000000000, -9000000000000], [0,
      9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([5265000000000], [1845000000000])
      (some (3, 1, 2)) (some (3, 1, 4)) (.next ([1905000000000], [705000000000]) (some (3, 1, 4))
      (some (3, 1, 4)) (.next ([3795000000000, -9000000000000], [2610000000000, 9000000000000])
      (some (3, 1, 4)) (some (3, 1, 4)) (.next ([2655000000000, 0], [2610000000000, 9000000000000])
      (some (3, 1, 4)) (some (3, 1, 4)) (.next ([2655000000000], [3750000000000]) (some (3, 1, 4))
      (some (3, 1, 4)) (.next ([2610000000000], [4500000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([0], [2655000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0, -9000000000000],
      [4500000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1845000000000], [7110000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-705000000000], [2610000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2610000000000, -9000000000000], [6405000000000]) (some (0, 2, 3))
      (some (0, 2, 3)) (.next ([-2610000000000, -9000000000000], [5265000000000, 9000000000000])
      (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3750000000000], [6405000000000]) (some (0, 2, 3))
      (some (0, 2, 3)) (.next ([-4500000000000], [7110000000000]) (some (0, 2, 3)) (some (0, 2, 3))
      (.terminal (some (0, 2, 3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded18_4
    · exact excluded18_5
    · exact (hj rfl).elim
    · exact excluded18_7
    · exact excluded18_8
    · exact excluded18_9
theorem next18 : model18.insert step18 = model19 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded19_0 : ExcludedOn (model19.B 0 ++ [step19.q]) 9000000000000 (model19.caps 0)
    (model19.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6129000000000, 2100000000000], [339000000000,
      2100000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next ([1773000000000, 4200000000000],
      [141000000000, -2100000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next ([4995000000000],
      [435000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next ([1860000000000], [195000000000])
      (some (5, 6, 6)) (some (5, 6, 6)) (.next ([4770000000000], [1035000000000]) (some (5, 6, 6))
      (some (5, 6, 6)) (.next ([7620000000000], [1740000000000]) (some (5, 6, 6)) (some (5, 6, 6))
      (.next ([7395000000000], [2340000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
      ([2625000000000], [1305000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([375000000000],
      [225000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([696000000000, -2100000000000],
      [663000000000, 4200000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([555000000000],
      [750000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([1266000000000, -2100000000000],
      [2001000000000, -2100000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([2175000000000],
      [4320000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([1575000000000], [4695000000000])
      (some (5, 6, 4)) (some (5, 6, 4)) fan19Owner0Part0)))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_4 : ExcludedOn (model19.B 4 ++ [step19.q]) 9000000000000 (model19.caps 4)
    (model19.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_5 : ExcludedOn (model19.B 5 ++ [step19.q]) 9000000000000 (model19.caps 5)
    (model19.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4515000000000, -9000000000000], [0,
      9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([5265000000000], [1860000000000])
      (some (3, 1, 2)) (some (3, 1, 4)) (.next ([1890000000000], [720000000000]) (some (3, 1, 4))
      (some (3, 1, 4)) (.next ([3795000000000, -9000000000000], [2610000000000, 9000000000000])
      (some (3, 1, 4)) (some (3, 1, 4)) (.next ([2655000000000, 0], [2610000000000, 9000000000000])
      (some (3, 1, 4)) (some (3, 1, 4)) (.next ([2655000000000], [3750000000000]) (some (3, 1, 4))
      (some (3, 1, 4)) (.next ([2610000000000], [4515000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([0], [2655000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0, -9000000000000],
      [4515000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1860000000000], [7125000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-720000000000], [2610000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2610000000000, -9000000000000], [6405000000000]) (some (0, 2, 3))
      (some (0, 2, 3)) (.next ([-2610000000000, -9000000000000], [5265000000000, 9000000000000])
      (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3750000000000], [6405000000000]) (some (0, 2, 3))
      (some (0, 2, 3)) (.next ([-4515000000000], [7125000000000]) (some (0, 2, 3)) (some (0, 2, 3))
      (.terminal (some (0, 2, 3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded19_4
    · exact excluded19_5
    · exact (hj rfl).elim
    · exact excluded19_7
    · exact excluded19_8
    · exact excluded19_9
theorem next19 : model19.insert step19 = model20 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded20_0 : ExcludedOn (model20.B 0 ++ [step20.q]) 9000000000000 (model20.caps 0)
    (model20.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6129000000000, 2100000000000], [339000000000,
      2100000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1773000000000, 4200000000000],
      [141000000000, -2100000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([4995000000000],
      [435000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([3948000000000], [357000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1860000000000], [195000000000]) (some (5, 1, 6))
      (some (5, 6, 6)) (.next ([4770000000000], [1035000000000]) (some (5, 6, 6)) (some (5, 6, 6))
      (.next ([6693000000000], [2880000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next
      ([6468000000000], [3480000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([375000000000],
      [225000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([696000000000, -2100000000000],
      [663000000000, 4200000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([555000000000],
      [750000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([1698000000000], [2445000000000])
      (some (5, 6, 4)) (some (5, 6, 4)) fan20Owner0Part0))))))))))))) (den := 9000000000000) (fuel
      := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5250000000000], [2088000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([5250000000000], [4698000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([2610000000000, 9000000000000], [2610000000000, 9000000000000]) (some
      (0, 3, 2)) (some (0, 3, 2)) (.next ([2640000000000, -9000000000000], [7308000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [2610000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-2088000000000, 9000000000000],
      [7338000000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-4698000000000],
      [9948000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2610000000000, -9000000000000],
      [5220000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-7308000000000,
      -9000000000000], [9948000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
      0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_2 : ExcludedOn (model20.B 2 ++ [step20.q]) 9000000000000 (model20.caps 2)
    (model20.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_3 : ExcludedOn (model20.B 3 ++ [step20.q]) 9000000000000 (model20.caps 3)
    (model20.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_4 : ExcludedOn (model20.B 4 ++ [step20.q]) 9000000000000 (model20.caps 4)
    (model20.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_5 : ExcludedOn (model20.B 5 ++ [step20.q]) 9000000000000 (model20.caps 5)
    (model20.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6405000000000], [1647000000000]) (some (3, 0,
      4)) (some (3, 1, 4)) (.next ([3795000000000, -9000000000000], [2610000000000, 9000000000000])
      (some (3, 1, 4)) (some (3, 1, 4)) (.next ([2103000000000], [1647000000000]) (some (3, 1, 4))
      (some (3, 1, 4)) (.next ([2655000000000, 0], [2610000000000, 9000000000000]) (some (3, 1, 4))
      (some (3, 1, 4)) (.next ([3750000000000], [4302000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([2655000000000], [3750000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([1140000000000, -9000000000000], [4302000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([0], [2655000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-1647000000000],
      [8052000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-2610000000000, -9000000000000],
      [6405000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1647000000000], [3750000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2610000000000, -9000000000000], [5265000000000,
      9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-4302000000000], [8052000000000])
      (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3750000000000], [6405000000000]) (some (0, 2, 3))
      (some (0, 2, 3)) (.next ([-4302000000000, 0], [5442000000000, -9000000000000]) (some (0, 2,
      3)) (some (0, 2, 3)) (.terminal (some (0, 2, 3)) (some (0, 4, 3)) (some (0, 4,
      3))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
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
    · exact excluded20_4
    · exact excluded20_5
    · exact (hj rfl).elim
    · exact excluded20_7
    · exact excluded20_8
    · exact excluded20_9
theorem next20 : model20.insert step20 = model21 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded21_0 : ExcludedOn (model21.B 0 ++ [step21.q]) 9000000000000 (model21.caps 0)
    (model21.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded21_4 : ExcludedOn (model21.B 4 ++ [step21.q]) 9000000000000 (model21.caps 4)
    (model21.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2460000000000], [15000000000]) (some (8, 0, 6))
      (some (8, 1, 6)) (.next ([2610000000000], [30000000000]) (some (8, 1, 6)) (some (8, 1, 6))
      (.next ([1677000000000], [33000000000]) (some (8, 1, 6)) (some (8, 1, 6)) (.next
      ([2880000000000], [120000000000]) (some (8, 1, 6)) (some (8, 1, 6)) (.next ([4950000000000],
      [300000000000]) (some (8, 1, 6)) (some (8, 1, 6)) (.next ([150000000000], [15000000000]) (some
      (8, 1, 6)) (some (8, 1, 6)) (.next ([3360000000000], [420000000000]) (some (8, 1, 6)) (some
      (9, 1, 6)) (.next ([2190000000000], [435000000000]) (some (9, 1, 6)) (some (9, 1, 6)) (.next
      ([4830000000000, 9000000000000], [1170000000000, -9000000000000]) (some (9, 1, 6)) (some (9,
      1, 6)) (.next ([420000000000], [105000000000]) (some (9, 1, 6)) (some (9, 1, 6)) (.next
      ([3735000000000], [963000000000]) (some (9, 1, 6)) (some (9, 1, 6)) (.next ([2730000000000],
      [750000000000]) (some (9, 1, 6)) (some (9, 1, 6)) (.next ([4407000000000], [1218000000000])
      (some (9, 1, 6)) (some (9, 1, 6)) (.next ([2025000000000], [585000000000]) (some (9, 1, 6))
      (some (9, 1, 6)) (.next ([270000000000], [90000000000]) (some (9, 1, 6)) (some (9, 1, 6))
      (.next ([2730000000000], [1185000000000]) (some (9, 1, 6)) (some (10, 1, 6)) (.next
      ([900000000000], [405000000000]) (some (10, 1, 6)) (some (10, 1, 6))
      fan21Owner4Part2))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded21_5 : ExcludedOn (model21.B 5 ++ [step21.q]) 9000000000000 (model21.caps 5)
    (model21.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_6 : ExcludedOn (model21.B 6 ++ [step21.q]) 9000000000000 (model21.caps 6)
    (model21.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_7 : ExcludedOn (model21.B 7 ++ [step21.q]) 9000000000000 (model21.caps 7)
    (model21.ord 7) 0 1 100 := by
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
    · exact excluded21_4
    · exact excluded21_5
    · exact excluded21_6
    · exact excluded21_7
    · exact (hj rfl).elim
    · exact excluded21_9
theorem next21 : model21.insert step21 = model22 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded22_0 : ExcludedOn (model22.B 0 ++ [step22.q]) 9000000000000 (model22.caps 0)
    (model22.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_5 : ExcludedOn (model22.B 5 ++ [step22.q]) 9000000000000 (model22.caps 5)
    (model22.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_6 : ExcludedOn (model22.B 6 ++ [step22.q]) 9000000000000 (model22.caps 6)
    (model22.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_7 : ExcludedOn (model22.B 7 ++ [step22.q]) 9000000000000 (model22.caps 7)
    (model22.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_8 : ExcludedOn (model22.B 8 ++ [step22.q]) 9000000000000 (model22.caps 8)
    (model22.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4935000000000], [2085000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([2355000000000], [1125000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([5895000000000], [3480000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1455000000000], [4440000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [7020000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2085000000000], [7020000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1125000000000], [3480000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-3480000000000], [9375000000000]) (some (0, 1, 2)) (some (0, 3, 2))
      (.next ([-4440000000000], [5895000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_6 : ExcludedOn (model23.B 6 ++ [step23.q]) 9000000000000 (model23.caps 6)
    (model23.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6390000000000], [1095000000000, 9000000000000])
      (some (5, 6, 2)) (some (5, 6, 3)) (.next ([4302000000000], [948000000000]) (some (5, 6, 3))
      (some (5, 6, 3)) (.next ([4515000000000], [1875000000000]) (some (5, 6, 3)) (some (5, 6, 3))
      fan23Owner6Part0)))) (den := 9000000000000) (fuel := 12)
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
    · exact (hj rfl).elim
    · exact excluded23_6
    · exact excluded23_7
    · exact excluded23_8
    · exact excluded23_9
theorem next23 : model23.insert step23 = model24 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint290000300000
end ConwaySoifer.Simplified.Certificates
