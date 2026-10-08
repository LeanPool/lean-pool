/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext140000150000
import Mathlib.Tactic.FinCases

/-!
# Sext 140000 150000 8

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
namespace Sext140000150000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan66Owner3Part0 : FanWitness := (.next ([-900000000000], [2340000000000]) (some (10, 5, 8))
    (some (10, 5, 8)) (.next ([-2700000000000, 9000000000000], [6210000000000]) (some (10, 5, 8))
    (some (10, 5, 8)) (.next ([-120000000000], [270000000000]) (some (10, 5, 8)) (some (10, 5, 8))
    (.next ([-4785000000000], [9900000000000]) (some (10, 5, 8)) (some (10, 6, 8)) (.next
    ([-2700000000000], [4725000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next ([-6225000000000,
    0], [10260000000000, 9000000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next
    ([-2880000000000], [4680000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next
    ([-3960000000000], [6210000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next
    ([-4575000000000], [6915000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next
    ([-3030000000000], [4560000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next ([-4110000000000,
    9000000000000], [6000000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next ([-6225000000000],
    [9000000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next ([-5040000000000], [6165000000000])
    (some (10, 6, 8)) (some (10, 6, 8)) (.next ([-5220000000000], [6120000000000]) (some (10, 6, 8))
    (some (10, 6, 8)) (.next ([-4740000000000], [5400000000000]) (some (10, 6, 8)) (some (10, 6, 8))
    (.next ([-5370000000000], [6000000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next
    ([-1515000000000], [1680000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next
    ([-2055000000000], [2250000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next ([-540000000000],
    [570000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next ([-3765000000000], [3960000000000])
    (some (10, 6, 8)) (some (10, 6, 8)) (.next ([-4890000000000], [5040000000000]) (some (10, 6, 8))
    (some (10, 6, 8)) (.next ([-5115000000000], [5220000000000]) (some (10, 6, 8)) (some (10, 6, 8))
    (.next ([-4770000000000], [4860000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next
    ([-2250000000000], [2280000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.terminal (some (10, 6,
    8)) (some (10, 6, 8)) (some (10, 6, 8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan66Owner3Part1 : FanWitness := (.next ([30000000000], [2250000000000]) (some (10, 10, 8))
    (some (10, 10, 8)) (.next ([0], [6015000000000]) (some (10, 10, 8)) (some (10, 10, 8)) (.next
    ([-15000000000], [6750000000000]) (some (10, 10, 8)) (some (10, 10, 8)) (.next ([-15000000000],
    [5385000000000]) (some (10, 3, 8)) (some (10, 3, 8)) (.next ([-15000000000], [5040000000000])
    (some (10, 3, 8)) (some (10, 3, 8)) (.next ([-15000000000], [3375000000000]) (some (10, 3, 8))
    (some (10, 3, 8)) (.next ([-60000000000], [7875000000000]) (some (10, 3, 8)) (some (10, 3, 8))
    (.next ([-45000000000], [4500000000000]) (some (10, 3, 8)) (some (10, 3, 8)) (.next
    ([-105000000000], [8100000000000]) (some (10, 3, 8)) (some (10, 3, 8)) (.next ([-45000000000],
    [2835000000000]) (some (10, 3, 8)) (some (10, 3, 8)) (.next ([-60000000000], [3600000000000])
    (some (10, 3, 8)) (some (10, 3, 8)) (.next ([-225000000000], [8370000000000]) (some (10, 3, 8))
    (some (10, 3, 8)) (.next ([-90000000000], [3060000000000]) (some (10, 3, 8)) (some (10, 3, 8))
    (.next ([-45000000000], [1125000000000]) (some (10, 3, 8)) (some (10, 3, 8)) (.next
    ([-180000000000], [3870000000000]) (some (10, 3, 8)) (some (10, 4, 8)) (.next ([-420000000000,
    9000000000000], [6180000000000]) (some (10, 4, 8)) (some (10, 4, 8)) (.next ([-210000000000],
    [2985000000000]) (some (10, 4, 8)) (some (10, 4, 8)) (.next ([-210000000000], [1620000000000])
    (some (10, 4, 8)) (some (10, 4, 8)) (.next ([-990000000000, 9000000000000], [6210000000000])
    (some (10, 4, 8)) (some (10, 4, 8)) (.next ([-45000000000], [225000000000]) (some (10, 4, 8))
    (some (10, 4, 8)) (.next ([-1680000000000], [6180000000000]) (some (10, 4, 8)) (some (10, 5, 8))
    (.next ([-165000000000], [495000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next
    ([-1620000000000], [4770000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next
    ([-2250000000000], [6210000000000]) (some (10, 5, 8)) (some (10, 5, 8))
    fan66Owner3Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan66Owner3Part2 : FanWitness := (.next ([3960000000000], [2250000000000]) (some (9, 10, 6))
    (some (9, 10, 6)) (.next ([1440000000000], [900000000000]) (some (9, 10, 6)) (some (9, 10, 6))
    (.next ([3510000000000, 9000000000000], [2700000000000, -9000000000000]) (some (9, 10, 6)) (some
    (9, 10, 6)) (.next ([150000000000], [120000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next
    ([5115000000000], [4785000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next ([2025000000000],
    [2700000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next ([4035000000000, 9000000000000],
    [6225000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next ([1800000000000], [2880000000000])
    (some (9, 10, 6)) (some (9, 10, 6)) (.next ([2250000000000], [3960000000000]) (some (9, 10, 6))
    (some (9, 10, 6)) (.next ([2340000000000], [4575000000000]) (some (9, 10, 6)) (some (9, 10, 6))
    (.next ([1530000000000], [3030000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next
    ([1890000000000, 9000000000000], [4110000000000, -9000000000000]) (some (9, 10, 6)) (some (9,
    10, 7)) (.next ([2775000000000], [6225000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next
    ([1125000000000], [5040000000000]) (some (9, 10, 7)) (some (10, 10, 8)) (.next ([900000000000],
    [5220000000000]) (some (10, 10, 8)) (some (10, 10, 8)) (.next ([660000000000], [4740000000000])
    (some (10, 10, 8)) (some (10, 10, 8)) (.next ([630000000000], [5370000000000]) (some (10, 10,
    8)) (some (10, 10, 8)) (.next ([165000000000], [1515000000000]) (some (10, 10, 8)) (some (10,
    10, 8)) (.next ([195000000000], [2055000000000]) (some (10, 10, 8)) (some (10, 10, 8)) (.next
    ([30000000000], [540000000000]) (some (10, 10, 8)) (some (10, 10, 8)) (.next ([195000000000],
    [3765000000000]) (some (10, 10, 8)) (some (10, 10, 8)) (.next ([150000000000], [4890000000000])
    (some (10, 10, 8)) (some (10, 10, 8)) (.next ([105000000000], [5115000000000]) (some (10, 10,
    8)) (some (10, 10, 8)) (.next ([90000000000], [4770000000000]) (some (10, 10, 8)) (some (10, 10,
    8)) fan66Owner3Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan68Owner2Part0 : FanWitness := (.next ([1125000000000], [5040000000000]) (some (0, 3, 4))
    (some (0, 3, 4)) (.next ([1260000000000, 9000000000000], [6195000000000, 0]) (some (0, 3, 4))
    (some (0, 3, 4)) (.next ([630000000000], [5370000000000]) (some (0, 3, 4)) (some (0, 3, 4))
    (.next ([15000000000], [3945000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([0],
    [6195000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-30000000000], [5070000000000])
    (some (0, 3, 4)) (some (0, 3, 5)) (.next ([-195000000000], [5565000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([-45000000000], [1125000000000]) (some (0, 3, 5)) (some (0, 3, 5))
    (.next ([-210000000000], [1620000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([-1230000000000, 9000000000000], [7740000000000, 0]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([-2490000000000], [7740000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-165000000000],
    [495000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-1740000000000], [4620000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-945000000000], [2490000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([-1575000000000], [4125000000000]) (some (0, 3, 5)) (some (6, 3, 5))
    (.next ([-2700000000000, 9000000000000], [6210000000000, 0]) (some (6, 3, 5)) (some (6, 3, 5))
    (.next ([-1530000000000], [3000000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-3780000000000, 9000000000000], [6165000000000, 0]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-3960000000000], [6210000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-4110000000000,
    9000000000000], [6000000000000, 0]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-5040000000000],
    [6165000000000]) (some (6, 3, 5)) (some (6, 4, 5)) (.next ([-6195000000000, 0], [7455000000000,
    9000000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-5370000000000], [6000000000000])
    (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-3945000000000], [3960000000000]) (some (6, 4, 5))
    (some (6, 4, 5)) (.terminal (some (6, 4, 5)) (some (6, 4, 0)) (some (6, 4,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan69Owner3Part0 : FanWitness := (.next ([-210000000000], [1620000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-45000000000], [225000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([-2565000000000, 9000000000000], [7740000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([-165000000000], [495000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([-1260000000000], [3750000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-1290000000000],
    [3675000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-1470000000000], [3630000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-2700000000000, 9000000000000], [6210000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-120000000000], [270000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-1620000000000], [3510000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([-3825000000000], [7740000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([-3765000000000], [7515000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-1740000000000],
    [3285000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-1620000000000], [3015000000000])
    (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-1575000000000], [2790000000000]) (some (0, 4, 6))
    (some (0, 4, 6)) (.next ([-3780000000000, 9000000000000], [6165000000000]) (some (0, 4, 6))
    (some (0, 4, 6)) (.next ([-3960000000000], [6210000000000]) (some (0, 4, 6)) (some (0, 4, 6))
    (.next ([-4110000000000, 9000000000000], [6000000000000]) (some (0, 4, 6)) (some (0, 4, 6))
    (.next ([-5040000000000], [6165000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next
    ([-6255000000000, 0], [7515000000000, 9000000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next
    ([-5220000000000], [6120000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-5370000000000],
    [6000000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-1530000000000], [1665000000000])
    (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-2490000000000, 9000000000000], [2490000000000])
    (some (0, 4, 6)) (some (0, 4, 6)) (.terminal (some (0, 4, 6)) (some (0, 4, 6)) (some (0, 4,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan69Owner3Part1 : FanWitness := (.next ([1890000000000], [1620000000000]) (some (7, 0, 4))
    (some (7, 0, 4)) (.next ([3915000000000], [3825000000000]) (some (7, 0, 4)) (some (7, 0, 5))
    (.next ([3750000000000], [3765000000000]) (some (7, 0, 5)) (some (7, 0, 5)) (.next
    ([1545000000000], [1740000000000]) (some (7, 0, 5)) (some (7, 0, 5)) (.next ([1395000000000],
    [1620000000000]) (some (7, 0, 5)) (some (7, 0, 5)) (.next ([1215000000000], [1575000000000])
    (some (7, 0, 5)) (some (7, 0, 5)) (.next ([2385000000000, 9000000000000], [3780000000000,
    -9000000000000]) (some (7, 0, 5)) (some (7, 0, 5)) (.next ([2250000000000], [3960000000000])
    (some (7, 0, 5)) (some (7, 8, 5)) (.next ([1890000000000, 9000000000000], [4110000000000,
    -9000000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([1125000000000], [5040000000000])
    (some (7, 8, 5)) (some (7, 8, 5)) (.next ([1260000000000, 9000000000000], [6255000000000]) (some
    (7, 8, 5)) (some (7, 8, 5)) (.next ([900000000000], [5220000000000]) (some (7, 8, 5)) (some (7,
    8, 5)) (.next ([630000000000], [5370000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next
    ([135000000000], [1530000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([0, 9000000000000],
    [2490000000000, -9000000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([0], [6255000000000])
    (some (7, 8, 5)) (some (7, 8, 6)) (.next ([-45000000000], [4005000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-75000000000], [5250000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([-90000000000], [5130000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([-135000000000], [5355000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-45000000000],
    [1125000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-255000000000], [5625000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-210000000000], [3720000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-90000000000], [1350000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    fan69Owner3Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan70Owner2Part0 : FanWitness := (.next ([1890000000000, 9000000000000], [4110000000000,
    -9000000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([1125000000000], [5040000000000])
    (some (0, 3, 4)) (some (0, 3, 4)) (.next ([1260000000000, 9000000000000], [6195000000000, 0])
    (some (0, 3, 4)) (some (0, 3, 4)) (.next ([630000000000], [5370000000000]) (some (0, 3, 4))
    (some (0, 3, 4)) (.next ([15000000000], [3945000000000]) (some (0, 3, 4)) (some (0, 3, 4))
    (.next ([0], [6195000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-30000000000],
    [5070000000000]) (some (0, 3, 4)) (some (0, 3, 5)) (.next ([-195000000000], [5565000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-45000000000], [1125000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([-210000000000], [1620000000000]) (some (0, 3, 5)) (some (0, 3, 5))
    (.next ([-1980000000000, 9000000000000], [7740000000000, 0]) (some (0, 3, 5)) (some (0, 3, 5))
    (.next ([-165000000000], [495000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([-3240000000000], [7740000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-2700000000000,
    9000000000000], [6210000000000, 0]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-1740000000000],
    [3870000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-1575000000000], [3375000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-1695000000000], [3240000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([-3780000000000, 9000000000000], [6165000000000, 0]) (some (0, 3, 5))
    (some (6, 3, 5)) (.next ([-3960000000000], [6210000000000]) (some (6, 3, 5)) (some (6, 3, 5))
    (.next ([-4110000000000, 9000000000000], [6000000000000, 0]) (some (6, 3, 5)) (some (6, 3, 5))
    (.next ([-5040000000000], [6165000000000]) (some (6, 3, 5)) (some (6, 4, 5)) (.next
    ([-6195000000000, 0], [7455000000000, 9000000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next
    ([-5370000000000], [6000000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-3945000000000],
    [3960000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.terminal (some (6, 4, 5)) (some (6, 4, 0))
    (some (6, 4, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan71Owner3Part0 : FanWitness := (.next ([-540000000000], [2925000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-45000000000], [225000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([-720000000000], [2880000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([-1260000000000], [4500000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-870000000000],
    [2760000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-1320000000000], [4110000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-165000000000], [495000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-3015000000000], [7515000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([-2700000000000, 9000000000000], [6210000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([-120000000000], [270000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([-3780000000000, 9000000000000], [6165000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([-3570000000000], [5760000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-3960000000000],
    [6210000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-5325000000000], [8070000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-4110000000000, 9000000000000], [6000000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-6810000000000, 9000000000000], [9000000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-5040000000000], [6165000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-6255000000000, 0], [7515000000000, 9000000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-2970000000000], [3510000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([-5220000000000], [6120000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([-5370000000000], [6000000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-8070000000000],
    [9000000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-2700000000000], [3000000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-3240000000000, 9000000000000], [3240000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.terminal (some (0, 8, 6)) (some (0, 8, 6)) (some (0, 8,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan71Owner3Part1 : FanWitness := (.next ([150000000000], [120000000000]) (some (7, 0, 8)) (some
    (7, 0, 8)) (.next ([2385000000000, 9000000000000], [3780000000000, -9000000000000]) (some (7, 0,
    8)) (some (7, 0, 8)) (.next ([2190000000000], [3570000000000]) (some (7, 0, 8)) (some (7, 0, 8))
    (.next ([2250000000000], [3960000000000]) (some (7, 0, 5)) (some (7, 0, 5)) (.next
    ([2745000000000], [5325000000000]) (some (7, 0, 5)) (some (7, 0, 5)) (.next ([1890000000000,
    9000000000000], [4110000000000, -9000000000000]) (some (7, 0, 5)) (some (7, 8, 5)) (.next
    ([2190000000000, 9000000000000], [6810000000000, -9000000000000]) (some (7, 8, 5)) (some (7, 8,
    5)) (.next ([1125000000000], [5040000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next
    ([1260000000000, 9000000000000], [6255000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next
    ([540000000000], [2970000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([900000000000],
    [5220000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([630000000000], [5370000000000])
    (some (7, 8, 5)) (some (7, 8, 5)) (.next ([930000000000], [8070000000000]) (some (7, 8, 5))
    (some (7, 8, 5)) (.next ([300000000000], [2700000000000]) (some (7, 8, 5)) (some (7, 8, 5))
    (.next ([0, 9000000000000], [3240000000000, -9000000000000]) (some (7, 8, 5)) (some (7, 8, 5))
    (.next ([0], [6255000000000]) (some (7, 8, 5)) (some (7, 8, 6)) (.next ([-45000000000],
    [4005000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-90000000000], [5130000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-135000000000], [5355000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-45000000000], [1125000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([-255000000000], [5625000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([-195000000000], [3030000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-90000000000],
    [1350000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-210000000000], [1620000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) fan71Owner3Part0))))))))))))))))))))))))

theorem excluded64_1 : ExcludedOn (model64.B 1 ++ [step64.q]) 9000000000000 (model64.caps 1)
    (model64.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7395000000000], [2130000000000]) (some (4, 5,
      1)) (some (4, 5, 2)) (.next ([3150000000000], [975000000000]) (some (4, 5, 2)) (some (4, 5,
      2)) (.next ([6102000000000], [2148000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
      ([1890000000000, -9000000000000], [975000000000, 0]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
      ([1260000000000, 9000000000000], [1260000000000, 9000000000000]) (some (4, 5, 2)) (some (4, 5,
      2)) (.next ([1875000000000], [2268000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
      ([1995000000000], [5115000000000, -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
      ([1995000000000], [6375000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([615000000000,
      -9000000000000], [2268000000000, 0]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([735000000000,
      -9000000000000], [7635000000000, 9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
      ([18000000000], [1275000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([0],
      [1260000000000, 9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([-2130000000000],
      [9525000000000]) (some (0, 5, 2)) (some (0, 5, 3)) (.next ([-975000000000], [4125000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2148000000000], [8250000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-975000000000, 0], [2865000000000, -9000000000000]) (some (0, 5, 3))
      (some (5, 5, 3)) (.next ([-1260000000000, -9000000000000], [2520000000000, 18000000000000])
      (some (5, 5, 3)) (some (5, 5, 4)) (.next ([-2268000000000], [4143000000000]) (some (5, 5, 4))
      (some (5, 5, 4)) (.next ([-5115000000000, 9000000000000], [7110000000000, -9000000000000])
      (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-6375000000000], [8370000000000]) (some (5, 1, 4))
      (some (5, 1, 4)) (.next ([-2268000000000, 0], [2883000000000, -9000000000000]) (some (5, 1,
      4)) (some (5, 1, 4)) (.next ([-7635000000000, -9000000000000], [8370000000000, 0]) (some (5,
      1, 4)) (some (5, 1, 4)) (.next ([-1275000000000], [1293000000000]) (some (5, 1, 4)) (some (5,
      1, 4)) (.terminal (some (5, 1, 4)) (some (5, 1, 4)) (some (5, 1, 4)))))))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded64_2 : ExcludedOn (model64.B 2 ++ [step64.q]) 9000000000000 (model64.caps 2)
    (model64.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded64_3 : ExcludedOn (model64.B 3 ++ [step64.q]) 9000000000000 (model64.caps 3)
    (model64.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded64_4 : ExcludedOn (model64.B 4 ++ [step64.q]) 9000000000000 (model64.caps 4)
    (model64.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded64_5 : ExcludedOn (model64.B 5 ++ [step64.q]) 9000000000000 (model64.caps 5)
    (model64.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded64_6 : ExcludedOn (model64.B 6 ++ [step64.q]) 9000000000000 (model64.caps 6)
    (model64.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1890000000000, 9000000000000], [735000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([1995000000000], [5115000000000,
      -9000000000000]) (some (2, 0, 2)) (some (2, 0, 2)) (.next ([630000000000], [1995000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([1260000000000, 9000000000000], [7740000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1260000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-735000000000, 9000000000000],
      [2625000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-5115000000000, 9000000000000],
      [7110000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1995000000000],
      [2625000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-7740000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded64_7 : ExcludedOn (model64.B 7 ++ [step64.q]) 9000000000000 (model64.caps 7)
    (model64.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded64_8 : ExcludedOn (model64.B 8 ++ [step64.q]) 9000000000000 (model64.caps 8)
    (model64.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded64_9 : ExcludedOn (model64.B 9 ++ [step64.q]) 9000000000000 (model64.caps 9)
    (model64.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked64 : StepValid model64 9000000000000 step64 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded64_1
    · exact excluded64_2
    · exact excluded64_3
    · exact excluded64_4
    · exact excluded64_5
    · exact excluded64_6
    · exact excluded64_7
    · exact excluded64_8
    · exact excluded64_9
theorem next64 : model64.insert step64 = model65 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded65_0 : ExcludedOn (model65.B 0 ++ [step65.q]) 9000000000000 (model65.caps 0)
    (model65.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded65_1 : ExcludedOn (model65.B 1 ++ [step65.q]) 9000000000000 (model65.caps 1)
    (model65.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3135000000000, 9000000000000], [1008000000000,
      -9000000000000]) (some (5, 0, 1)) (some (5, 0, 5)) (.next ([1890000000000, -9000000000000],
      [975000000000, 0]) (some (5, 0, 5)) (some (5, 1, 5)) (.next ([1260000000000, 9000000000000],
      [1260000000000, 9000000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([4125000000000],
      [4170000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([1875000000000], [2268000000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([4143000000000], [5445000000000]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([615000000000, -9000000000000], [2268000000000, 0]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([1260000000000, 9000000000000], [6060000000000, -9000000000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([285000000000, 9000000000000], [4125000000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([18000000000], [1275000000000]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([0], [1260000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1,
      5)) (.next ([-1008000000000, 9000000000000], [4143000000000]) (some (0, 1, 5)) (some (0, 1,
      5)) (.next ([-975000000000, 0], [2865000000000, -9000000000000]) (some (0, 1, 5)) (some (0, 1,
      5)) (.next ([-1260000000000, -9000000000000], [2520000000000, 18000000000000]) (some (0, 1,
      5)) (some (0, 1, 5)) (.next ([-4170000000000], [8295000000000]) (some (0, 1, 5)) (some (0, 1,
      5)) (.next ([-2268000000000], [4143000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-5445000000000], [9588000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2268000000000,
      0], [2883000000000, -9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-6060000000000, 9000000000000], [7320000000000, 0]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-4125000000000], [4410000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-1275000000000], [1293000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.terminal (some (0, 1,
      5)) (some (0, 1, 5)) (some (0, 1, 5))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded65_2 : ExcludedOn (model65.B 2 ++ [step65.q]) 9000000000000 (model65.caps 2)
    (model65.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded65_3 : ExcludedOn (model65.B 3 ++ [step65.q]) 9000000000000 (model65.caps 3)
    (model65.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded65_4 : ExcludedOn (model65.B 4 ++ [step65.q]) 9000000000000 (model65.caps 4)
    (model65.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded65_5 : ExcludedOn (model65.B 5 ++ [step65.q]) 9000000000000 (model65.caps 5)
    (model65.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded65_6 : ExcludedOn (model65.B 6 ++ [step65.q]) 9000000000000 (model65.caps 6)
    (model65.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded65_8 : ExcludedOn (model65.B 8 ++ [step65.q]) 9000000000000 (model65.caps 8)
    (model65.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded65_9 : ExcludedOn (model65.B 9 ++ [step65.q]) 9000000000000 (model65.caps 9)
    (model65.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked65 : StepValid model65 9000000000000 step65 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded65_0
    · exact excluded65_1
    · exact excluded65_2
    · exact excluded65_3
    · exact excluded65_4
    · exact excluded65_5
    · exact excluded65_6
    · exact (hj rfl).elim
    · exact excluded65_8
    · exact excluded65_9
theorem next65 : model65.insert step65 = model66 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded66_0 : ExcludedOn (model66.B 0 ++ [step66.q]) 9000000000000 (model66.caps 0)
    (model66.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded66_1 : ExcludedOn (model66.B 1 ++ [step66.q]) 9000000000000 (model66.caps 1)
    (model66.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded66_2 : ExcludedOn (model66.B 2 ++ [step66.q]) 9000000000000 (model66.caps 2)
    (model66.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded66_3 : ExcludedOn (model66.B 3 ++ [step66.q]) 9000000000000 (model66.caps 3)
    (model66.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6735000000000], [15000000000]) (some (8, 10, 6))
      (some (9, 10, 6)) (.next ([5370000000000], [15000000000]) (some (9, 10, 6)) (some (9, 10, 6))
      (.next ([5025000000000], [15000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next
      ([3360000000000], [15000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next ([7815000000000],
      [60000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next ([4455000000000], [45000000000])
      (some (9, 10, 6)) (some (9, 10, 6)) (.next ([7995000000000], [105000000000]) (some (9, 10, 6))
      (some (9, 10, 6)) (.next ([2790000000000], [45000000000]) (some (9, 10, 6)) (some (9, 10, 6))
      (.next ([3540000000000], [60000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next
      ([8145000000000], [225000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next ([2970000000000],
      [90000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next ([1080000000000], [45000000000])
      (some (9, 10, 6)) (some (9, 10, 6)) (.next ([3690000000000], [180000000000]) (some (9, 10, 6))
      (some (9, 10, 6)) (.next ([5760000000000, 9000000000000], [420000000000, -9000000000000])
      (some (9, 10, 6)) (some (9, 10, 6)) (.next ([2775000000000], [210000000000]) (some (9, 10, 6))
      (some (9, 10, 6)) (.next ([1410000000000], [210000000000]) (some (9, 10, 6)) (some (9, 10, 6))
      (.next ([5220000000000, 9000000000000], [990000000000, -9000000000000]) (some (9, 10, 6))
      (some (9, 10, 6)) (.next ([180000000000], [45000000000]) (some (9, 10, 6)) (some (9, 10, 6))
      (.next ([4500000000000], [1680000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next
      ([330000000000], [165000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next ([3150000000000],
      [1620000000000]) (some (9, 10, 6)) (some (9, 10, 6)) fan66Owner3Part2))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded66_4 : ExcludedOn (model66.B 4 ++ [step66.q]) 9000000000000 (model66.caps 4)
    (model66.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1515000000000, -9000000000000], [1260000000000,
      9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([2775000000000], [6870000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1335000000000], [5535000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([0], [5535000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-1260000000000, -9000000000000], [2775000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-6870000000000], [9645000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-5535000000000], [6870000000000]) (some (4, 1, 2)) (some (4, 1, 4)) (.terminal (some (4, 1,
      4)) (some (0, 2, 4)) (some (4, 2, 4))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded66_5 : ExcludedOn (model66.B 5 ++ [step66.q]) 9000000000000 (model66.caps 5)
    (model66.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded66_6 : ExcludedOn (model66.B 6 ++ [step66.q]) 9000000000000 (model66.caps 6)
    (model66.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded66_7 : ExcludedOn (model66.B 7 ++ [step66.q]) 9000000000000 (model66.caps 7)
    (model66.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded66_9 : ExcludedOn (model66.B 9 ++ [step66.q]) 9000000000000 (model66.caps 9)
    (model66.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked66 : StepValid model66 9000000000000 step66 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded66_0
    · exact excluded66_1
    · exact excluded66_2
    · exact excluded66_3
    · exact excluded66_4
    · exact excluded66_5
    · exact excluded66_6
    · exact excluded66_7
    · exact (hj rfl).elim
    · exact excluded66_9
theorem next66 : model66.insert step66 = model67 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded67_0 : ExcludedOn (model67.B 0 ++ [step67.q]) 9000000000000 (model67.caps 0)
    (model67.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded67_1 : ExcludedOn (model67.B 1 ++ [step67.q]) 9000000000000 (model67.caps 1)
    (model67.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded67_2 : ExcludedOn (model67.B 2 ++ [step67.q]) 9000000000000 (model67.caps 2)
    (model67.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded67_4 : ExcludedOn (model67.B 4 ++ [step67.q]) 9000000000000 (model67.caps 4)
    (model67.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2745000000000], [4125000000000]) (some (4, 0,
      2)) (some (4, 1, 2)) (.next ([2745000000000], [5535000000000]) (some (4, 1, 2)) (some (4, 1,
      2)) (.next ([1335000000000], [5535000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0],
      [5535000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-4125000000000], [6870000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5535000000000], [8280000000000]) (some (0, 1, 2))
      (some (0, 1, 4)) (.next ([-5535000000000], [6870000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.terminal (some (0, 1, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded67_5 : ExcludedOn (model67.B 5 ++ [step67.q]) 9000000000000 (model67.caps 5)
    (model67.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded67_6 : ExcludedOn (model67.B 6 ++ [step67.q]) 9000000000000 (model67.caps 6)
    (model67.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded67_7 : ExcludedOn (model67.B 7 ++ [step67.q]) 9000000000000 (model67.caps 7)
    (model67.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded67_8 : ExcludedOn (model67.B 8 ++ [step67.q]) 9000000000000 (model67.caps 8)
    (model67.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4725000000000], [1530000000000]) (some (0, 0,
      4)) (some (0, 1, 4)) (.next ([6255000000000], [2745000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([3105000000000], [1650000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1500000000000], [5850000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1125000000000],
      [4725000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1245000000000], [6225000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([120000000000], [1500000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([30000000000], [2745000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([0], [6225000000000]) (some (0, 1, 3)) (some (0, 4, 3)) (.next ([-1530000000000],
      [6255000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-2745000000000], [9000000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1650000000000], [4755000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-5850000000000], [7350000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-4725000000000], [5850000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-6225000000000], [7470000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-1500000000000], [1620000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-2745000000000], [2775000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4,
      3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded67_9 : ExcludedOn (model67.B 9 ++ [step67.q]) 9000000000000 (model67.caps 9)
    (model67.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked67 : StepValid model67 9000000000000 step67 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded67_0
    · exact excluded67_1
    · exact excluded67_2
    · exact (hj rfl).elim
    · exact excluded67_4
    · exact excluded67_5
    · exact excluded67_6
    · exact excluded67_7
    · exact excluded67_8
    · exact excluded67_9
theorem next67 : model67.insert step67 = model68 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded68_0 : ExcludedOn (model68.B 0 ++ [step68.q]) 9000000000000 (model68.caps 0)
    (model68.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded68_1 : ExcludedOn (model68.B 1 ++ [step68.q]) 9000000000000 (model68.caps 1)
    (model68.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded68_2 : ExcludedOn (model68.B 2 ++ [step68.q]) 9000000000000 (model68.caps 2)
    (model68.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5040000000000], [30000000000]) (some (0, 6, 4))
      (some (0, 6, 4)) (.next ([5370000000000], [195000000000]) (some (0, 6, 4)) (some (0, 6, 4))
      (.next ([1080000000000], [45000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
      ([1410000000000], [210000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([6510000000000,
      9000000000000], [1230000000000, -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
      ([5250000000000], [2490000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([330000000000],
      [165000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([2880000000000], [1740000000000])
      (some (0, 6, 4)) (some (0, 6, 4)) (.next ([1545000000000], [945000000000]) (some (0, 3, 4))
      (some (0, 3, 4)) (.next ([2550000000000], [1575000000000]) (some (0, 3, 4)) (some (0, 3, 4))
      (.next ([3510000000000, 9000000000000], [2700000000000, -9000000000000]) (some (0, 3, 4))
      (some (0, 3, 4)) (.next ([1470000000000], [1530000000000]) (some (0, 3, 4)) (some (0, 3, 4))
      (.next ([2385000000000, 9000000000000], [3780000000000, -9000000000000]) (some (0, 3, 4))
      (some (0, 3, 4)) (.next ([2250000000000], [3960000000000]) (some (0, 3, 4)) (some (0, 3, 4))
      (.next ([1890000000000, 9000000000000], [4110000000000, -9000000000000]) (some (0, 3, 4))
      (some (0, 3, 4)) fan68Owner2Part0)))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded68_4 : ExcludedOn (model68.B 4 ++ [step68.q]) 9000000000000 (model68.caps 4)
    (model68.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded68_5 : ExcludedOn (model68.B 5 ++ [step68.q]) 9000000000000 (model68.caps 5)
    (model68.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded68_6 : ExcludedOn (model68.B 6 ++ [step68.q]) 9000000000000 (model68.caps 6)
    (model68.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded68_7 : ExcludedOn (model68.B 7 ++ [step68.q]) 9000000000000 (model68.caps 7)
    (model68.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded68_8 : ExcludedOn (model68.B 8 ++ [step68.q]) 9000000000000 (model68.caps 8)
    (model68.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded68_9 : ExcludedOn (model68.B 9 ++ [step68.q]) 9000000000000 (model68.caps 9)
    (model68.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked68 : StepValid model68 9000000000000 step68 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded68_0
    · exact excluded68_1
    · exact excluded68_2
    · exact (hj rfl).elim
    · exact excluded68_4
    · exact excluded68_5
    · exact excluded68_6
    · exact excluded68_7
    · exact excluded68_8
    · exact excluded68_9
theorem next68 : model68.insert step68 = model69 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded69_0 : ExcludedOn (model69.B 0 ++ [step69.q]) 9000000000000 (model69.caps 0)
    (model69.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded69_1 : ExcludedOn (model69.B 1 ++ [step69.q]) 9000000000000 (model69.caps 1)
    (model69.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded69_2 : ExcludedOn (model69.B 2 ++ [step69.q]) 9000000000000 (model69.caps 2)
    (model69.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded69_3 : ExcludedOn (model69.B 3 ++ [step69.q]) 9000000000000 (model69.caps 3)
    (model69.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3960000000000], [45000000000]) (some (6, 0, 4))
      (some (7, 0, 4)) (.next ([5175000000000], [75000000000]) (some (7, 0, 4)) (some (7, 0, 4))
      (.next ([5040000000000], [90000000000]) (some (7, 0, 4)) (some (7, 0, 4)) (.next
      ([5220000000000], [135000000000]) (some (7, 0, 4)) (some (7, 0, 4)) (.next ([1080000000000],
      [45000000000]) (some (7, 0, 4)) (some (7, 0, 4)) (.next ([5370000000000], [255000000000])
      (some (7, 0, 4)) (some (7, 0, 4)) (.next ([3510000000000], [210000000000]) (some (7, 0, 4))
      (some (7, 0, 4)) (.next ([1260000000000], [90000000000]) (some (7, 0, 4)) (some (7, 0, 4))
      (.next ([1410000000000], [210000000000]) (some (7, 0, 4)) (some (7, 0, 4)) (.next
      ([180000000000], [45000000000]) (some (7, 0, 4)) (some (7, 0, 4)) (.next ([5175000000000,
      9000000000000], [2565000000000, -9000000000000]) (some (7, 0, 4)) (some (7, 0, 4)) (.next
      ([330000000000], [165000000000]) (some (7, 0, 4)) (some (7, 0, 4)) (.next ([2490000000000],
      [1260000000000]) (some (7, 0, 4)) (some (7, 0, 4)) (.next ([2385000000000], [1290000000000])
      (some (7, 0, 4)) (some (7, 0, 4)) (.next ([2160000000000], [1470000000000]) (some (7, 0, 4))
      (some (7, 0, 4)) (.next ([3510000000000, 9000000000000], [2700000000000, -9000000000000])
      (some (7, 0, 4)) (some (7, 0, 4)) (.next ([150000000000], [120000000000]) (some (7, 0, 4))
      (some (7, 0, 4)) fan69Owner3Part1)))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded69_5 : ExcludedOn (model69.B 5 ++ [step69.q]) 9000000000000 (model69.caps 5)
    (model69.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded69_6 : ExcludedOn (model69.B 6 ++ [step69.q]) 9000000000000 (model69.caps 6)
    (model69.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded69_7 : ExcludedOn (model69.B 7 ++ [step69.q]) 9000000000000 (model69.caps 7)
    (model69.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded69_8 : ExcludedOn (model69.B 8 ++ [step69.q]) 9000000000000 (model69.caps 8)
    (model69.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded69_9 : ExcludedOn (model69.B 9 ++ [step69.q]) 9000000000000 (model69.caps 9)
    (model69.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked69 : StepValid model69 9000000000000 step69 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded69_0
    · exact excluded69_1
    · exact excluded69_2
    · exact excluded69_3
    · exact (hj rfl).elim
    · exact excluded69_5
    · exact excluded69_6
    · exact excluded69_7
    · exact excluded69_8
    · exact excluded69_9
theorem next69 : model69.insert step69 = model70 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded70_0 : ExcludedOn (model70.B 0 ++ [step70.q]) 9000000000000 (model70.caps 0)
    (model70.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded70_1 : ExcludedOn (model70.B 1 ++ [step70.q]) 9000000000000 (model70.caps 1)
    (model70.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded70_2 : ExcludedOn (model70.B 2 ++ [step70.q]) 9000000000000 (model70.caps 2)
    (model70.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5040000000000], [30000000000]) (some (0, 6, 4))
      (some (0, 6, 4)) (.next ([5370000000000], [195000000000]) (some (0, 6, 4)) (some (0, 6, 4))
      (.next ([1080000000000], [45000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
      ([1410000000000], [210000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([5760000000000,
      9000000000000], [1980000000000, -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
      ([330000000000], [165000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([4500000000000],
      [3240000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([3510000000000, 9000000000000],
      [2700000000000, -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([2130000000000],
      [1740000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([1800000000000], [1575000000000])
      (some (0, 3, 4)) (some (0, 3, 4)) (.next ([1545000000000], [1695000000000]) (some (0, 3, 4))
      (some (0, 3, 4)) (.next ([2385000000000, 9000000000000], [3780000000000, -9000000000000])
      (some (0, 3, 4)) (some (0, 3, 4)) (.next ([2250000000000], [3960000000000]) (some (0, 3, 4))
      (some (0, 3, 4)) fan70Owner2Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded70_4 : ExcludedOn (model70.B 4 ++ [step70.q]) 9000000000000 (model70.caps 4)
    (model70.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded70_5 : ExcludedOn (model70.B 5 ++ [step70.q]) 9000000000000 (model70.caps 5)
    (model70.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded70_6 : ExcludedOn (model70.B 6 ++ [step70.q]) 9000000000000 (model70.caps 6)
    (model70.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded70_7 : ExcludedOn (model70.B 7 ++ [step70.q]) 9000000000000 (model70.caps 7)
    (model70.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded70_8 : ExcludedOn (model70.B 8 ++ [step70.q]) 9000000000000 (model70.caps 8)
    (model70.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded70_9 : ExcludedOn (model70.B 9 ++ [step70.q]) 9000000000000 (model70.caps 9)
    (model70.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked70 : StepValid model70 9000000000000 step70 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded70_0
    · exact excluded70_1
    · exact excluded70_2
    · exact (hj rfl).elim
    · exact excluded70_4
    · exact excluded70_5
    · exact excluded70_6
    · exact excluded70_7
    · exact excluded70_8
    · exact excluded70_9
theorem next70 : model70.insert step70 = model71 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded71_1 : ExcludedOn (model71.B 1 ++ [step71.q]) 9000000000000 (model71.caps 1)
    (model71.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded71_2 : ExcludedOn (model71.B 2 ++ [step71.q]) 9000000000000 (model71.caps 2)
    (model71.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded71_3 : ExcludedOn (model71.B 3 ++ [step71.q]) 9000000000000 (model71.caps 3)
    (model71.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3960000000000], [45000000000]) (some (6, 0, 8))
      (some (7, 0, 8)) (.next ([5040000000000], [90000000000]) (some (7, 0, 8)) (some (7, 0, 8))
      (.next ([5220000000000], [135000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next
      ([1080000000000], [45000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([5370000000000],
      [255000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([2835000000000], [195000000000])
      (some (7, 0, 8)) (some (7, 0, 8)) (.next ([1260000000000], [90000000000]) (some (7, 0, 8))
      (some (7, 0, 8)) (.next ([1410000000000], [210000000000]) (some (7, 0, 8)) (some (7, 0, 8))
      (.next ([2385000000000], [540000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next
      ([180000000000], [45000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([2160000000000],
      [720000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([3240000000000], [1260000000000])
      (some (7, 0, 8)) (some (7, 0, 8)) (.next ([1890000000000], [870000000000]) (some (7, 0, 8))
      (some (7, 0, 8)) (.next ([2790000000000], [1320000000000]) (some (7, 0, 8)) (some (7, 0, 8))
      (.next ([330000000000], [165000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next
      ([4500000000000], [3015000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([3510000000000,
      9000000000000], [2700000000000, -9000000000000]) (some (7, 0, 8)) (some (7, 0, 8))
      fan71Owner3Part1)))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded71_4 : ExcludedOn (model71.B 4 ++ [step71.q]) 9000000000000 (model71.caps 4)
    (model71.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3825000000000], [1260000000000]) (some (4, 0,
      5)) (some (4, 1, 5)) (.next ([5085000000000], [1710000000000]) (some (4, 1, 5)) (some (4, 1,
      5)) (.next ([1260000000000], [1785000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([2535000000000], [5535000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1260000000000],
      [2985000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1335000000000], [5535000000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1260000000000, 9000000000000], [6810000000000,
      -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0, 9000000000000], [3825000000000,
      -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0], [5535000000000]) (some (4, 1,
      5)) (some (4, 1, 5)) (.next ([-1260000000000], [5085000000000]) (some (0, 1, 5)) (some (0, 1,
      5)) (.next ([-1710000000000], [6795000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-1785000000000], [3045000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-5535000000000], [8070000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-2985000000000], [4245000000000]) (some (0, 1, 5)) (some (0, 5, 5)) (.next
      ([-5535000000000], [6870000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-6810000000000,
      9000000000000], [8070000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3825000000000,
      9000000000000], [3825000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3))
      (some (0, 5, 4)) (some (0, 5, 4))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded71_5 : ExcludedOn (model71.B 5 ++ [step71.q]) 9000000000000 (model71.caps 5)
    (model71.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8070000000000], [930000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([4995000000000], [630000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([630000000000], [1107000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([2445000000000], [5925000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([375000000000],
      [1260000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1635000000000], [6357000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1260000000000, 9000000000000], [6732000000000, 0])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1338000000000], [7662000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([630000000000, 9000000000000], [5625000000000, 0]) (some (5, 1, 2))
      (some (5, 1, 5)) (.next ([330000000000, 9000000000000], [7740000000000, -9000000000000]) (some
      (5, 1, 5)) (some (5, 1, 5)) (.next ([0, 0], [1260000000000, 9000000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([-930000000000], [9000000000000]) (some (0, 1, 5)) (some (0, 2, 5))
      (.next ([-630000000000], [5625000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-1107000000000], [1737000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-5925000000000], [8370000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-1260000000000], [1635000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-6357000000000], [7992000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-6732000000000,
      0], [7992000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-7662000000000], [9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5625000000000,
      0], [6255000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-7740000000000,
      9000000000000], [8070000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2,
      5)) (some (0, 2, 5)) (some (0, 2, 5))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded71_6 : ExcludedOn (model71.B 6 ++ [step71.q]) 9000000000000 (model71.caps 6)
    (model71.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded71_7 : ExcludedOn (model71.B 7 ++ [step71.q]) 9000000000000 (model71.caps 7)
    (model71.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded71_8 : ExcludedOn (model71.B 8 ++ [step71.q]) 9000000000000 (model71.caps 8)
    (model71.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded71_9 : ExcludedOn (model71.B 9 ++ [step71.q]) 9000000000000 (model71.caps 9)
    (model71.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked71 : StepValid model71 9000000000000 step71 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded71_1
    · exact excluded71_2
    · exact excluded71_3
    · exact excluded71_4
    · exact excluded71_5
    · exact excluded71_6
    · exact excluded71_7
    · exact excluded71_8
    · exact excluded71_9
theorem next71 : model71.insert step71 = model72 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext140000150000
end ConwaySoifer.Simplified.Certificates
