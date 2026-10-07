/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext140000150000
import Mathlib.Tactic.FinCases

/-!
# Sext 140000 150000 9

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
def fan72Owner2Part0 : FanWitness := (.next ([1125000000000], [5040000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([1260000000000, 9000000000000], [6195000000000, 0]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([630000000000], [5370000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([420000000000], [8205000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([15000000000], [3945000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([0], [6195000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-30000000000], [5070000000000]) (some (0, 6, 4))
    (some (0, 6, 5)) (.next ([-195000000000], [5565000000000]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-45000000000], [1125000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-210000000000], [2835000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-210000000000],
    [1620000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-705000000000], [3165000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-165000000000], [495000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-2700000000000, 9000000000000], [6210000000000, 0]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-3780000000000, 9000000000000], [6165000000000, 0]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-3960000000000], [6210000000000]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-4110000000000, 9000000000000], [6000000000000, 0]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-5775000000000], [8205000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-6945000000000, 9000000000000], [8625000000000, 0]) (some (0, 6, 5)) (some (6, 6, 5)) (.next
    ([-5040000000000], [6165000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-6195000000000,
    0], [7455000000000, 9000000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-5370000000000],
    [6000000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-8205000000000], [8625000000000])
    (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-3945000000000], [3960000000000]) (some (6, 4, 5))
    (some (6, 4, 5)) (.terminal (some (6, 4, 5)) (some (6, 4, 0)) (some (6, 4,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan72Owner3Part0 : FanWitness := (.next ([-540000000000], [2925000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-45000000000], [225000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([-720000000000], [2880000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([-1260000000000], [4500000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-1005000000000],
    [3210000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-870000000000], [2760000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-165000000000], [495000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-1275000000000], [3360000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([-3015000000000], [7515000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([-1500000000000], [3540000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-120000000000],
    [270000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-2625000000000], [4620000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-3780000000000, 9000000000000], [6165000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-3960000000000], [6210000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-4110000000000, 9000000000000], [6000000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-6630000000000], [8580000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([-5040000000000], [6165000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([-4080000000000], [4965000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-6255000000000,
    0], [7515000000000, 9000000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-2970000000000],
    [3510000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-5220000000000], [6120000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-7320000000000, 9000000000000], [8205000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-5370000000000], [6000000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-3240000000000, 9000000000000], [3240000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.terminal (some (0, 8, 6)) (some (0, 8, 6)) (some (0, 8,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan72Owner3Part1 : FanWitness := (.next ([2040000000000], [1500000000000]) (some (7, 0, 8))
    (some (7, 0, 8)) (.next ([150000000000], [120000000000]) (some (7, 0, 8)) (some (7, 0, 8))
    (.next ([1995000000000], [2625000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next
    ([2385000000000, 9000000000000], [3780000000000, -9000000000000]) (some (7, 0, 8)) (some (7, 0,
    8)) (.next ([2250000000000], [3960000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next
    ([1890000000000, 9000000000000], [4110000000000, -9000000000000]) (some (7, 0, 8)) (some (7, 0,
    8)) (.next ([1950000000000], [6630000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next
    ([1125000000000], [5040000000000]) (some (7, 0, 8)) (some (7, 8, 8)) (.next ([885000000000],
    [4080000000000]) (some (7, 8, 8)) (some (7, 8, 8)) (.next ([1260000000000, 9000000000000],
    [6255000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([540000000000], [2970000000000])
    (some (7, 8, 5)) (some (7, 8, 5)) (.next ([900000000000], [5220000000000]) (some (7, 8, 5))
    (some (7, 8, 5)) (.next ([885000000000, 9000000000000], [7320000000000, -9000000000000]) (some
    (7, 8, 5)) (some (7, 8, 5)) (.next ([630000000000], [5370000000000]) (some (7, 8, 5)) (some (7,
    8, 5)) (.next ([0, 9000000000000], [3240000000000, -9000000000000]) (some (7, 8, 5)) (some (7,
    8, 5)) (.next ([0], [6255000000000]) (some (7, 8, 5)) (some (7, 8, 6)) (.next ([-45000000000],
    [4005000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-90000000000], [5130000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-135000000000], [5355000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-45000000000], [1125000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([-375000000000], [8580000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([-255000000000], [5625000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-90000000000],
    [1350000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-210000000000], [1620000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) fan72Owner3Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan73Owner0Part0 : FanWitness := (.next ([-1920000000000], [5460000000000]) (some (0, 4, 8))
    (some (0, 4, 8)) (.next ([-2250000000000], [5970000000000]) (some (0, 4, 8)) (some (0, 4, 8))
    (.next ([-1830000000000], [4290000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next
    ([-3960000000000], [8730000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next ([-4215000000000],
    [8625000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next ([-375000000000], [750000000000])
    (some (0, 4, 8)) (some (0, 4, 8)) (.next ([-1530000000000], [2835000000000]) (some (0, 4, 8))
    (some (0, 4, 8)) (.next ([-465000000000], [795000000000]) (some (0, 4, 8)) (some (0, 4, 8))
    (.next ([-795000000000], [1305000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next
    ([-1890000000000], [3090000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next ([-3585000000000],
    [5595000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next ([-330000000000], [510000000000])
    (some (0, 4, 8)) (some (0, 4, 8)) (.next ([-4410000000000], [6420000000000]) (some (0, 4, 8))
    (some (0, 4, 8)) (.next ([-4335000000000], [5970000000000]) (some (0, 4, 8)) (some (0, 4, 8))
    (.next ([-5160000000000], [6795000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next
    ([-1530000000000], [2010000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next ([-1890000000000],
    [2265000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next ([-4665000000000], [5505000000000])
    (some (0, 4, 8)) (some (0, 4, 8)) (.next ([-5490000000000], [6330000000000]) (some (0, 4, 8))
    (some (0, 4, 8)) (.next ([-6420000000000], [6900000000000]) (some (0, 4, 8)) (some (0, 4, 8))
    (.next ([-4845000000000], [5175000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next
    ([-5670000000000], [6000000000000]) (some (0, 4, 8)) (some (1, 4, 8)) (.next ([-6675000000000],
    [6795000000000]) (some (1, 4, 8)) (some (1, 4, 8)) (.next ([-7170000000000], [7275000000000])
    (some (1, 4, 8)) (some (1, 4, 8)) (.terminal (some (1, 4, 8)) (some (1, 4, 8)) (some (1, 4,
    8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan73Owner0Part1 : FanWitness := (.next ([2010000000000], [4410000000000]) (some (0, 2, 8))
    (some (0, 2, 8)) (.next ([1635000000000], [4335000000000]) (some (0, 2, 8)) (some (0, 2, 8))
    (.next ([1635000000000], [5160000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next
    ([480000000000], [1530000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([375000000000],
    [1890000000000]) (some (0, 2, 8)) (some (0, 3, 8)) (.next ([840000000000], [4665000000000])
    (some (0, 3, 8)) (some (0, 3, 8)) (.next ([840000000000], [5490000000000]) (some (0, 3, 8))
    (some (0, 3, 8)) (.next ([480000000000], [6420000000000]) (some (0, 3, 8)) (some (0, 3, 8))
    (.next ([330000000000], [4845000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next
    ([330000000000], [5670000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([120000000000],
    [6675000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([105000000000], [7170000000000])
    (some (0, 3, 8)) (some (0, 3, 8)) (.next ([0], [825000000000]) (some (0, 3, 8)) (some (0, 3, 8))
    (.next ([-255000000000], [7425000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next
    ([-90000000000], [1170000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-690000000000],
    [7500000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-1050000000000], [7755000000000])
    (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-1125000000000], [7425000000000]) (some (0, 3, 8))
    (some (0, 3, 8)) (.next ([-1200000000000], [7680000000000]) (some (0, 3, 8)) (some (0, 3, 8))
    (.next ([-1560000000000], [7935000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next
    ([-1950000000000], [8250000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-420000000000],
    [1680000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-105000000000], [360000000000])
    (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-1455000000000], [4665000000000]) (some (0, 3, 8))
    (some (0, 4, 8)) fan73Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan73Owner2Part0 : FanWitness := (.next ([1125000000000], [5040000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([1260000000000, 9000000000000], [6195000000000, 0]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([630000000000], [5370000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([15000000000], [3945000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([0],
    [6195000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-30000000000], [5070000000000])
    (some (0, 6, 4)) (some (0, 6, 5)) (.next ([-195000000000], [5565000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-45000000000], [1125000000000]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-210000000000], [1620000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-2235000000000], [8985000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-1530000000000,
    9000000000000], [5490000000000, -9000000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-165000000000], [495000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-2790000000000],
    [6750000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-2700000000000, 9000000000000],
    [6210000000000, 0]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-2250000000000], [5040000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-2205000000000], [3915000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-2040000000000], [3420000000000]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-3780000000000, 9000000000000], [6165000000000, 0]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-3960000000000], [6210000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-4110000000000, 9000000000000], [6000000000000, 0]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-5040000000000], [6165000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-6195000000000,
    0], [7455000000000, 9000000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-5370000000000],
    [6000000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-3945000000000], [3960000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.terminal (some (0, 6, 5)) (some (1, 6, 0)) (some (1, 6,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan74Owner2Part0 : FanWitness := (.next ([1125000000000], [5040000000000]) (some (0, 3, 4))
    (some (0, 3, 4)) (.next ([1260000000000, 9000000000000], [6195000000000, 0]) (some (0, 3, 4))
    (some (0, 3, 4)) (.next ([630000000000], [5370000000000]) (some (0, 3, 4)) (some (0, 3, 4))
    (.next ([15000000000], [3945000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([0],
    [6195000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-30000000000], [5070000000000])
    (some (0, 3, 4)) (some (0, 3, 5)) (.next ([-195000000000], [5565000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([-45000000000], [1125000000000]) (some (0, 3, 5)) (some (0, 3, 5))
    (.next ([-540000000000], [5580000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([-210000000000], [1620000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-1620000000000],
    [5535000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-165000000000], [495000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-1950000000000], [5370000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([-2700000000000, 9000000000000], [6210000000000, 0]) (some (0, 3, 5))
    (some (0, 6, 5)) (.next ([-3780000000000, 9000000000000], [6165000000000, 0]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-5565000000000], [8985000000000]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-3960000000000], [6210000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-4110000000000, 9000000000000], [6000000000000, 0]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-1530000000000, 9000000000000], [2160000000000, -9000000000000]) (some (0, 6, 5)) (some (0, 6,
    5)) (.next ([-2790000000000], [3420000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-5040000000000], [6165000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-6195000000000,
    0], [7455000000000, 9000000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-5370000000000],
    [6000000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-3945000000000], [3960000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.terminal (some (0, 6, 5)) (some (1, 6, 0)) (some (1, 6,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan75Owner0Part0 : FanWitness := (.next ([-2040000000000], [4800000000000]) (some (0, 4, 5))
    (some (0, 4, 5)) (.next ([-3960000000000], [8250000000000]) (some (0, 4, 5)) (some (0, 4, 5))
    (.next ([-375000000000], [750000000000]) (some (0, 4, 5)) (some (0, 4, 5)) (.next
    ([-4470000000000], [8430000000000]) (some (0, 4, 5)) (some (0, 4, 6)) (.next ([-1530000000000],
    [2835000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-465000000000], [795000000000])
    (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-795000000000], [1305000000000]) (some (0, 4, 6))
    (some (0, 4, 6)) (.next ([-1890000000000], [3090000000000]) (some (0, 4, 6)) (some (0, 4, 6))
    (.next ([-3585000000000], [5595000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next
    ([-330000000000], [510000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-4410000000000],
    [6420000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-4335000000000], [5970000000000])
    (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-5160000000000], [6795000000000]) (some (0, 4, 6))
    (some (0, 4, 6)) (.next ([-1530000000000], [2010000000000]) (some (0, 4, 6)) (some (0, 4, 6))
    (.next ([-2520000000000], [3270000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next
    ([-2415000000000], [2910000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-1890000000000],
    [2265000000000]) (some (0, 4, 6)) (some (0, 8, 6)) (.next ([-4665000000000], [5505000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-5490000000000], [6330000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-6420000000000], [6900000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([-4845000000000], [5175000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([-5670000000000], [6000000000000]) (some (0, 8, 6)) (some (1, 8, 6)) (.next ([-6675000000000],
    [6795000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-7170000000000], [7275000000000])
    (some (1, 8, 6)) (some (1, 8, 6)) (.terminal (some (1, 8, 6)) (some (1, 8, 6)) (some (1, 8,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan75Owner0Part1 : FanWitness := (.next ([1635000000000], [5160000000000]) (some (0, 2, 8))
    (some (0, 2, 8)) (.next ([480000000000], [1530000000000]) (some (0, 2, 8)) (some (0, 2, 8))
    (.next ([750000000000], [2520000000000]) (some (0, 2, 8)) (some (0, 3, 8)) (.next
    ([495000000000], [2415000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([375000000000],
    [1890000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([840000000000], [4665000000000])
    (some (0, 3, 8)) (some (0, 3, 8)) (.next ([840000000000], [5490000000000]) (some (0, 3, 8))
    (some (0, 3, 8)) (.next ([480000000000], [6420000000000]) (some (0, 3, 8)) (some (0, 3, 8))
    (.next ([330000000000], [4845000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next
    ([330000000000], [5670000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([120000000000],
    [6675000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([105000000000], [7170000000000])
    (some (0, 3, 8)) (some (0, 3, 8)) (.next ([0], [825000000000]) (some (0, 3, 8)) (some (0, 3, 8))
    (.next ([-255000000000], [7425000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next
    ([-90000000000], [1170000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-690000000000],
    [7500000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-1050000000000], [7755000000000])
    (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-1200000000000], [7680000000000]) (some (0, 3, 8))
    (some (0, 3, 8)) (.next ([-1560000000000], [7935000000000]) (some (0, 3, 8)) (some (0, 3, 8))
    (.next ([-420000000000], [1680000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next
    ([-1215000000000], [4800000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-105000000000],
    [360000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-2790000000000], [7170000000000])
    (some (0, 3, 8)) (some (0, 4, 8)) (.next ([-3165000000000], [7920000000000]) (some (0, 4, 5))
    (some (0, 4, 5)) fan75Owner0Part0))))))))))))))))))))))))

theorem excluded72_1 : ExcludedOn (model72.B 1 ++ [step72.q]) 9000000000000 (model72.caps 1)
    (model72.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded72_2 : ExcludedOn (model72.B 2 ++ [step72.q]) 9000000000000 (model72.caps 2)
    (model72.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5040000000000], [30000000000]) (some (0, 6, 4))
      (some (0, 6, 4)) (.next ([5370000000000], [195000000000]) (some (0, 6, 4)) (some (0, 6, 4))
      (.next ([1080000000000], [45000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
      ([2625000000000], [210000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([1410000000000],
      [210000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([2460000000000], [705000000000])
      (some (0, 6, 4)) (some (0, 6, 4)) (.next ([330000000000], [165000000000]) (some (0, 6, 4))
      (some (0, 6, 4)) (.next ([3510000000000, 9000000000000], [2700000000000, -9000000000000])
      (some (0, 6, 4)) (some (0, 6, 4)) (.next ([2385000000000, 9000000000000], [3780000000000,
      -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([2250000000000], [3960000000000])
      (some (0, 6, 4)) (some (0, 6, 4)) (.next ([1890000000000, 9000000000000], [4110000000000,
      -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([2430000000000], [5775000000000])
      (some (0, 6, 4)) (some (0, 6, 4)) (.next ([1680000000000, 9000000000000], [6945000000000,
      -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) fan72Owner2Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded72_3 : ExcludedOn (model72.B 3 ++ [step72.q]) 9000000000000 (model72.caps 3)
    (model72.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3960000000000], [45000000000]) (some (6, 0, 8))
      (some (7, 0, 8)) (.next ([5040000000000], [90000000000]) (some (7, 0, 8)) (some (7, 0, 8))
      (.next ([5220000000000], [135000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next
      ([1080000000000], [45000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([8205000000000],
      [375000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([5370000000000], [255000000000])
      (some (7, 0, 8)) (some (7, 0, 8)) (.next ([1260000000000], [90000000000]) (some (7, 0, 8))
      (some (7, 0, 8)) (.next ([1410000000000], [210000000000]) (some (7, 0, 8)) (some (7, 0, 8))
      (.next ([2385000000000], [540000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next
      ([180000000000], [45000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([2160000000000],
      [720000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([3240000000000], [1260000000000])
      (some (7, 0, 8)) (some (7, 0, 8)) (.next ([2205000000000], [1005000000000]) (some (7, 0, 8))
      (some (7, 0, 8)) (.next ([1890000000000], [870000000000]) (some (7, 0, 8)) (some (7, 0, 8))
      (.next ([330000000000], [165000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next
      ([2085000000000], [1275000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([4500000000000],
      [3015000000000]) (some (7, 0, 8)) (some (7, 0, 8)) fan72Owner3Part1)))))))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded72_4 : ExcludedOn (model72.B 4 ++ [step72.q]) 9000000000000 (model72.caps 4)
    (model72.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded72_5 : ExcludedOn (model72.B 5 ++ [step72.q]) 9000000000000 (model72.caps 5)
    (model72.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded72_6 : ExcludedOn (model72.B 6 ++ [step72.q]) 9000000000000 (model72.caps 6)
    (model72.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded72_7 : ExcludedOn (model72.B 7 ++ [step72.q]) 9000000000000 (model72.caps 7)
    (model72.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded72_8 : ExcludedOn (model72.B 8 ++ [step72.q]) 9000000000000 (model72.caps 8)
    (model72.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded72_9 : ExcludedOn (model72.B 9 ++ [step72.q]) 9000000000000 (model72.caps 9)
    (model72.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked72 : StepValid model72 9000000000000 step72 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded72_1
    · exact excluded72_2
    · exact excluded72_3
    · exact excluded72_4
    · exact excluded72_5
    · exact excluded72_6
    · exact excluded72_7
    · exact excluded72_8
    · exact excluded72_9
theorem next72 : model72.insert step72 = model73 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded73_0 : ExcludedOn (model73.B 0 ++ [step73.q]) 9000000000000 (model73.caps 0)
    (model73.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7170000000000], [255000000000]) (some (8, 1, 4))
      (some (8, 2, 4)) (.next ([1080000000000], [90000000000]) (some (8, 2, 4)) (some (8, 2, 4))
      (.next ([6810000000000], [690000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
      ([6705000000000], [1050000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([6300000000000],
      [1125000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([6480000000000], [1200000000000])
      (some (8, 2, 4)) (some (8, 2, 4)) (.next ([6375000000000], [1560000000000]) (some (8, 2, 4))
      (some (8, 2, 4)) (.next ([6300000000000], [1950000000000]) (some (8, 2, 4)) (some (8, 2, 4))
      (.next ([1260000000000], [420000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
      ([255000000000], [105000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([3210000000000],
      [1455000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([3540000000000], [1920000000000])
      (some (6, 2, 4)) (some (6, 2, 4)) (.next ([3720000000000], [2250000000000]) (some (6, 2, 4))
      (some (6, 2, 4)) (.next ([2460000000000], [1830000000000]) (some (6, 2, 4)) (some (6, 2, 4))
      (.next ([4770000000000], [3960000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
      ([4410000000000], [4215000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([375000000000],
      [375000000000]) (some (6, 2, 4)) (some (6, 2, 8)) (.next ([1305000000000], [1530000000000])
      (some (6, 2, 8)) (some (6, 2, 8)) (.next ([330000000000], [465000000000]) (some (6, 2, 8))
      (some (6, 2, 8)) (.next ([510000000000], [795000000000]) (some (6, 2, 8)) (some (7, 2, 8))
      (.next ([1200000000000], [1890000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
      ([2010000000000], [3585000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([180000000000],
      [330000000000]) (some (7, 2, 8)) (some (7, 2, 8)) fan73Owner0Part1))))))))))))))))))))))))
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded73_2 : ExcludedOn (model73.B 2 ++ [step73.q]) 9000000000000 (model73.caps 2)
    (model73.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5040000000000], [30000000000]) (some (0, 1, 6))
      (some (0, 1, 6)) (.next ([5370000000000], [195000000000]) (some (0, 1, 6)) (some (0, 1, 6))
      (.next ([1080000000000], [45000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
      ([1410000000000], [210000000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next ([6750000000000],
      [2235000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([3960000000000, 0], [1530000000000,
      -9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([330000000000], [165000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([3960000000000], [2790000000000]) (some (0, 2, 4))
      (some (0, 3, 4)) (.next ([3510000000000, 9000000000000], [2700000000000, -9000000000000])
      (some (0, 3, 4)) (some (0, 3, 4)) (.next ([2790000000000], [2250000000000]) (some (0, 3, 4))
      (some (0, 3, 4)) (.next ([1710000000000], [2205000000000]) (some (0, 3, 4)) (some (0, 3, 4))
      (.next ([1380000000000], [2040000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
      ([2385000000000, 9000000000000], [3780000000000, -9000000000000]) (some (0, 3, 4)) (some (0,
      6, 4)) (.next ([2250000000000], [3960000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
      ([1890000000000, 9000000000000], [4110000000000, -9000000000000]) (some (0, 6, 4)) (some (0,
      6, 4)) fan73Owner2Part0)))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded73_3 : ExcludedOn (model73.B 3 ++ [step73.q]) 9000000000000 (model73.caps 3)
    (model73.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded73_4 : ExcludedOn (model73.B 4 ++ [step73.q]) 9000000000000 (model73.caps 4)
    (model73.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded73_5 : ExcludedOn (model73.B 5 ++ [step73.q]) 9000000000000 (model73.caps 5)
    (model73.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded73_6 : ExcludedOn (model73.B 6 ++ [step73.q]) 9000000000000 (model73.caps 6)
    (model73.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded73_7 : ExcludedOn (model73.B 7 ++ [step73.q]) 9000000000000 (model73.caps 7)
    (model73.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded73_8 : ExcludedOn (model73.B 8 ++ [step73.q]) 9000000000000 (model73.caps 8)
    (model73.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded73_9 : ExcludedOn (model73.B 9 ++ [step73.q]) 9000000000000 (model73.caps 9)
    (model73.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked73 : StepValid model73 9000000000000 step73 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded73_0
    · exact (hj rfl).elim
    · exact excluded73_2
    · exact excluded73_3
    · exact excluded73_4
    · exact excluded73_5
    · exact excluded73_6
    · exact excluded73_7
    · exact excluded73_8
    · exact excluded73_9
theorem next73 : model73.insert step73 = model74 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded74_0 : ExcludedOn (model74.B 0 ++ [step74.q]) 9000000000000 (model74.caps 0)
    (model74.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded74_2 : ExcludedOn (model74.B 2 ++ [step74.q]) 9000000000000 (model74.caps 2)
    (model74.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5040000000000], [30000000000]) (some (0, 1, 6))
      (some (0, 1, 6)) (.next ([5370000000000], [195000000000]) (some (0, 1, 6)) (some (0, 1, 6))
      (.next ([1080000000000], [45000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
      ([5040000000000], [540000000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next ([1410000000000],
      [210000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([3915000000000], [1620000000000])
      (some (0, 2, 6)) (some (0, 2, 6)) (.next ([330000000000], [165000000000]) (some (0, 2, 6))
      (some (0, 2, 6)) (.next ([3420000000000], [1950000000000]) (some (0, 2, 6)) (some (0, 3, 6))
      (.next ([3510000000000, 9000000000000], [2700000000000, -9000000000000]) (some (0, 3, 6))
      (some (0, 3, 6)) (.next ([2385000000000, 9000000000000], [3780000000000, -9000000000000])
      (some (0, 3, 6)) (some (0, 3, 6)) (.next ([3420000000000], [5565000000000]) (some (0, 3, 6))
      (some (0, 3, 6)) (.next ([2250000000000], [3960000000000]) (some (0, 3, 6)) (some (0, 3, 6))
      (.next ([1890000000000, 9000000000000], [4110000000000, -9000000000000]) (some (0, 3, 6))
      (some (0, 3, 6)) (.next ([630000000000, 0], [1530000000000, -9000000000000]) (some (0, 3, 6))
      (some (0, 3, 6)) (.next ([630000000000], [2790000000000]) (some (0, 3, 4)) (some (0, 3, 4))
      fan74Owner2Part0)))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded74_3 : ExcludedOn (model74.B 3 ++ [step74.q]) 9000000000000 (model74.caps 3)
    (model74.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded74_4 : ExcludedOn (model74.B 4 ++ [step74.q]) 9000000000000 (model74.caps 4)
    (model74.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded74_5 : ExcludedOn (model74.B 5 ++ [step74.q]) 9000000000000 (model74.caps 5)
    (model74.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded74_6 : ExcludedOn (model74.B 6 ++ [step74.q]) 9000000000000 (model74.caps 6)
    (model74.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded74_7 : ExcludedOn (model74.B 7 ++ [step74.q]) 9000000000000 (model74.caps 7)
    (model74.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6210000000000], [1740000000000]) (some (0, 3,
      1)) (some (0, 3, 2)) (.next ([6210000000000], [3420000000000]) (some (0, 3, 2)) (some (0, 3,
      2)) (.next ([1680000000000], [3180000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next
      ([1350000000000], [3420000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0],
      [4860000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-1740000000000], [7950000000000])
      (some (3, 3, 2)) (some (3, 3, 2)) (.next ([-3420000000000], [9630000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-3180000000000], [4860000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-3420000000000], [4770000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some
      (3, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded74_8 : ExcludedOn (model74.B 8 ++ [step74.q]) 9000000000000 (model74.caps 8)
    (model74.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded74_9 : ExcludedOn (model74.B 9 ++ [step74.q]) 9000000000000 (model74.caps 9)
    (model74.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked74 : StepValid model74 9000000000000 step74 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded74_0
    · exact (hj rfl).elim
    · exact excluded74_2
    · exact excluded74_3
    · exact excluded74_4
    · exact excluded74_5
    · exact excluded74_6
    · exact excluded74_7
    · exact excluded74_8
    · exact excluded74_9
theorem next74 : model74.insert step74 = model75 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded75_0 : ExcludedOn (model75.B 0 ++ [step75.q]) 9000000000000 (model75.caps 0)
    (model75.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7170000000000], [255000000000]) (some (6, 1, 8))
      (some (6, 2, 8)) (.next ([1080000000000], [90000000000]) (some (6, 2, 8)) (some (6, 2, 8))
      (.next ([6810000000000], [690000000000]) (some (6, 2, 8)) (some (6, 2, 8)) (.next
      ([6705000000000], [1050000000000]) (some (6, 2, 8)) (some (6, 2, 8)) (.next ([6480000000000],
      [1200000000000]) (some (6, 2, 8)) (some (6, 2, 8)) (.next ([6375000000000], [1560000000000])
      (some (6, 2, 8)) (some (6, 2, 8)) (.next ([1260000000000], [420000000000]) (some (6, 2, 8))
      (some (6, 2, 8)) (.next ([3585000000000], [1215000000000]) (some (6, 2, 8)) (some (6, 2, 8))
      (.next ([255000000000], [105000000000]) (some (6, 2, 8)) (some (6, 2, 8)) (.next
      ([4380000000000], [2790000000000]) (some (6, 2, 8)) (some (6, 2, 8)) (.next ([4755000000000],
      [3165000000000]) (some (6, 2, 8)) (some (6, 2, 8)) (.next ([2760000000000], [2040000000000])
      (some (6, 2, 8)) (some (6, 2, 8)) (.next ([4290000000000], [3960000000000]) (some (6, 2, 8))
      (some (6, 2, 8)) (.next ([375000000000], [375000000000]) (some (6, 2, 8)) (some (6, 2, 8))
      (.next ([3960000000000], [4470000000000]) (some (6, 2, 8)) (some (6, 2, 8)) (.next
      ([1305000000000], [1530000000000]) (some (6, 2, 8)) (some (6, 2, 8)) (.next ([330000000000],
      [465000000000]) (some (6, 2, 8)) (some (6, 2, 8)) (.next ([510000000000], [795000000000])
      (some (6, 2, 8)) (some (7, 2, 8)) (.next ([1200000000000], [1890000000000]) (some (7, 2, 8))
      (some (7, 2, 8)) (.next ([2010000000000], [3585000000000]) (some (7, 2, 8)) (some (7, 2, 8))
      (.next ([180000000000], [330000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
      ([2010000000000], [4410000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([1635000000000],
      [4335000000000]) (some (0, 2, 8)) (some (0, 2, 8)) fan75Owner0Part1))))))))))))))))))))))))
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded75_2 : ExcludedOn (model75.B 2 ++ [step75.q]) 9000000000000 (model75.caps 2)
    (model75.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded75_3 : ExcludedOn (model75.B 3 ++ [step75.q]) 9000000000000 (model75.caps 3)
    (model75.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded75_4 : ExcludedOn (model75.B 4 ++ [step75.q]) 9000000000000 (model75.caps 4)
    (model75.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded75_5 : ExcludedOn (model75.B 5 ++ [step75.q]) 9000000000000 (model75.caps 5)
    (model75.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded75_6 : ExcludedOn (model75.B 6 ++ [step75.q]) 9000000000000 (model75.caps 6)
    (model75.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4800000000000, 9000000000000], [240000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([3540000000000], [1500000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1500000000000], [2700000000000, -9000000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1260000000000, 9000000000000], [7740000000000,
      -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1260000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-240000000000, 9000000000000],
      [5040000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-1500000000000], [5040000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2700000000000, 9000000000000], [4200000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-7740000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded75_7 : ExcludedOn (model75.B 7 ++ [step75.q]) 9000000000000 (model75.caps 7)
    (model75.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded75_8 : ExcludedOn (model75.B 8 ++ [step75.q]) 9000000000000 (model75.caps 8)
    (model75.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded75_9 : ExcludedOn (model75.B 9 ++ [step75.q]) 9000000000000 (model75.caps 9)
    (model75.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked75 : StepValid model75 9000000000000 step75 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded75_0
    · exact (hj rfl).elim
    · exact excluded75_2
    · exact excluded75_3
    · exact excluded75_4
    · exact excluded75_5
    · exact excluded75_6
    · exact excluded75_7
    · exact excluded75_8
    · exact excluded75_9
theorem next75 : model75.insert step75 = model76 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext140000150000
end ConwaySoifer.Simplified.Certificates
