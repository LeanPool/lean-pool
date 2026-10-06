/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext240000250000
import Mathlib.Tactic.FinCases

/-!
# Sext 240000 250000 4

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
namespace Sext240000250000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner3Part0 : FanWitness := (.next ([2160000000000, 9000000000000], [4455000000000,
    -9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([1935000000000], [4125000000000])
    (some (5, 6, 3)) (some (5, 6, 4)) (.next ([1770000000000], [4125000000000]) (some (5, 6, 4))
    (some (5, 6, 4)) (.next ([1605000000000, 9000000000000], [4680000000000]) (some (5, 6, 4)) (some
    (5, 6, 4)) (.next ([990000000000], [3090000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
    ([1440000000000, 9000000000000], [4845000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([0],
    [2760000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([-225000000000], [3750000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-555000000000], [4680000000000]) (some (0, 3, 4))
    (some (0, 3, 4)) (.next ([-930000000000, 9000000000000], [6840000000000]) (some (0, 3, 4)) (some
    (0, 3, 4)) (.next ([-375000000000], [2535000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
    ([-720000000000], [4845000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-375000000000],
    [2370000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-555000000000], [1920000000000])
    (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-720000000000], [2085000000000]) (some (0, 3, 4))
    (some (1, 3, 4)) (.next ([-2760000000000], [6615000000000]) (some (1, 3, 4)) (some (1, 3, 4))
    (.next ([-3090000000000], [6840000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next
    ([-2760000000000, 0], [4920000000000, 9000000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next
    ([-4455000000000, 9000000000000], [6615000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next
    ([-4125000000000], [6060000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-4125000000000],
    [5895000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-4680000000000, 0], [6285000000000,
    9000000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-3090000000000], [4080000000000])
    (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-4845000000000, 0], [6285000000000, 9000000000000])
    (some (1, 3, 4)) (some (1, 3, 4)) (.terminal (some (1, 3, 4)) (some (1, 3, 4)) (some (1, 3,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner3Part0 : FanWitness := (.next ([2160000000000, 9000000000000], [2760000000000]) (some
    (5, 2, 3)) (some (5, 2, 6)) (.next ([2820000000000], [4680000000000]) (some (5, 2, 6)) (some (5,
    2, 6)) (.next ([2655000000000], [4845000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next
    ([2160000000000, 9000000000000], [4455000000000, -9000000000000]) (some (5, 2, 6)) (some (5, 2,
    6)) (.next ([1935000000000], [4125000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next
    ([1770000000000], [4125000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([1605000000000,
    9000000000000], [4680000000000]) (some (5, 2, 6)) (some (5, 3, 6)) (.next ([1440000000000,
    9000000000000], [4845000000000]) (some (5, 3, 6)) (some (5, 3, 6)) (.next ([0], [2760000000000])
    (some (5, 3, 6)) (some (5, 3, 6)) (.next ([-555000000000], [4680000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-720000000000], [4845000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([-555000000000], [1920000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-720000000000], [2085000000000]) (some (0, 3, 6)) (some (1, 3, 6)) (.next ([-2760000000000],
    [6615000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-2760000000000], [6135000000000])
    (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-3240000000000], [6615000000000]) (some (1, 3, 6))
    (some (1, 3, 6)) (.next ([-2760000000000, 0], [4920000000000, 9000000000000]) (some (1, 3, 6))
    (some (1, 3, 6)) (.next ([-4680000000000], [7500000000000]) (some (1, 3, 6)) (some (1, 3, 6))
    (.next ([-4845000000000], [7500000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next
    ([-4455000000000, 9000000000000], [6615000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next
    ([-4125000000000], [6060000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-4125000000000],
    [5895000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-4680000000000, 0], [6285000000000,
    9000000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-4845000000000, 0], [6285000000000,
    9000000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.terminal (some (1, 3, 6)) (some (1, 3, 4))
    (some (1, 3, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner3Part0 : FanWitness := (.next ([2520000000000], [4875000000000]) (some (5, 6, 3))
    (some (5, 6, 3)) (.next ([2160000000000, 9000000000000], [4455000000000, -9000000000000]) (some
    (5, 6, 3)) (some (5, 6, 3)) (.next ([1935000000000], [4125000000000]) (some (5, 6, 3)) (some (5,
    6, 4)) (.next ([1770000000000], [4125000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
    ([1605000000000, 9000000000000], [4680000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
    ([1440000000000, 9000000000000], [4845000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([0],
    [2760000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([-240000000000], [4875000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-555000000000], [4680000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-720000000000], [4845000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-555000000000], [1920000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-780000000000], [2520000000000]) (some (0, 6, 4)) (some (1, 6, 4)) (.next ([-720000000000],
    [2085000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-2715000000000, 9000000000000],
    [7395000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-1605000000000], [4320000000000])
    (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-1605000000000], [4155000000000]) (some (1, 3, 4))
    (some (1, 3, 4)) (.next ([-2760000000000], [6615000000000]) (some (1, 3, 4)) (some (1, 3, 4))
    (.next ([-2760000000000, 0], [4920000000000, 9000000000000]) (some (1, 3, 4)) (some (1, 3, 4))
    (.next ([-4875000000000], [7395000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next
    ([-4455000000000, 9000000000000], [6615000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next
    ([-4125000000000], [6060000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-4125000000000],
    [5895000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-4680000000000, 0], [6285000000000,
    9000000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-4845000000000, 0], [6285000000000,
    9000000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.terminal (some (1, 3, 4)) (some (1, 3, 4))
    (some (1, 3, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner3Part0 : FanWitness := (.next ([2487000000000], [2625000000000]) (some (5, 2, 6))
    (some (5, 2, 6)) (.next ([2160000000000, 9000000000000], [2760000000000]) (some (5, 2, 6)) (some
    (5, 2, 6)) (.next ([2160000000000, 9000000000000], [4455000000000, -9000000000000]) (some (5, 2,
    6)) (some (5, 2, 6)) (.next ([1935000000000], [4125000000000]) (some (5, 2, 6)) (some (5, 2, 6))
    (.next ([1770000000000], [4125000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next
    ([1605000000000, 9000000000000], [4680000000000]) (some (5, 2, 6)) (some (5, 3, 6)) (.next
    ([1440000000000, 9000000000000], [4845000000000]) (some (5, 3, 6)) (some (5, 3, 6)) (.next ([0],
    [2760000000000]) (some (5, 3, 6)) (some (5, 3, 6)) (.next ([-273000000000], [5385000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-555000000000], [4680000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-465000000000, 9000000000000], [2952000000000, -9000000000000]) (some
    (0, 3, 6)) (some (0, 3, 6)) (.next ([-555000000000], [1920000000000]) (some (0, 3, 4)) (some (0,
    3, 4)) (.next ([-2193000000000], [6750000000000]) (some (0, 3, 4)) (some (1, 3, 4)) (.next
    ([-720000000000], [2085000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-2358000000000],
    [6750000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-1503000000000], [4128000000000])
    (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-2760000000000], [6615000000000]) (some (1, 3, 4))
    (some (1, 3, 4)) (.next ([-2625000000000], [5112000000000]) (some (1, 3, 4)) (some (1, 3, 4))
    (.next ([-2760000000000, 0], [4920000000000, 9000000000000]) (some (1, 3, 4)) (some (1, 3, 4))
    (.next ([-4455000000000, 9000000000000], [6615000000000]) (some (1, 3, 4)) (some (1, 3, 4))
    (.next ([-4125000000000], [6060000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next
    ([-4125000000000], [5895000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-4680000000000,
    0], [6285000000000, 9000000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-4845000000000,
    0], [6285000000000, 9000000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.terminal (some (1, 3,
    4)) (some (1, 3, 4)) (some (1, 3, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan36Owner3Part0 : FanWitness := (.next ([2160000000000, 9000000000000], [4455000000000,
    -9000000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([1935000000000], [4125000000000])
    (some (5, 2, 6)) (some (5, 2, 6)) (.next ([1770000000000], [4125000000000]) (some (5, 2, 6))
    (some (5, 2, 6)) (.next ([1605000000000, 9000000000000], [4680000000000]) (some (5, 2, 6)) (some
    (5, 3, 6)) (.next ([1440000000000, 9000000000000], [4845000000000]) (some (5, 3, 6)) (some (5,
    3, 6)) (.next ([615000000000], [5145000000000]) (some (5, 3, 6)) (some (5, 3, 6)) (.next ([0],
    [2760000000000]) (some (5, 3, 6)) (some (5, 3, 6)) (.next ([-225000000000, 9000000000000],
    [3600000000000, -9000000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-555000000000],
    [4680000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-720000000000], [4845000000000])
    (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-1305000000000], [6510000000000]) (some (0, 3, 4))
    (some (0, 3, 4)) (.next ([-1470000000000], [6510000000000]) (some (0, 3, 4)) (some (0, 3, 4))
    (.next ([-855000000000], [3240000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
    ([-555000000000], [1920000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-720000000000],
    [2085000000000]) (some (0, 3, 4)) (some (1, 3, 4)) (.next ([-2385000000000], [5760000000000])
    (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-2760000000000], [6615000000000]) (some (1, 3, 4))
    (some (1, 3, 4)) (.next ([-2760000000000, 0], [4920000000000, 9000000000000]) (some (1, 3, 4))
    (some (1, 3, 4)) (.next ([-4455000000000, 9000000000000], [6615000000000]) (some (1, 3, 4))
    (some (1, 3, 4)) (.next ([-4125000000000], [6060000000000]) (some (1, 3, 4)) (some (1, 3, 4))
    (.next ([-4125000000000], [5895000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next
    ([-4680000000000, 0], [6285000000000, 9000000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next
    ([-4845000000000, 0], [6285000000000, 9000000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next
    ([-5145000000000], [5760000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.terminal (some (1, 3,
    4)) (some (1, 3, 4)) (some (1, 3, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner3Part0 : FanWitness := (.next ([2160000000000, 9000000000000], [4455000000000,
    -9000000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([1935000000000], [4125000000000])
    (some (5, 2, 6)) (some (5, 2, 6)) (.next ([1770000000000], [4125000000000]) (some (5, 2, 6))
    (some (5, 2, 6)) (.next ([1920000000000], [5205000000000]) (some (5, 2, 6)) (some (5, 3, 6))
    (.next ([1605000000000, 9000000000000], [4680000000000]) (some (5, 3, 6)) (some (5, 3, 6))
    (.next ([1440000000000, 9000000000000], [4845000000000]) (some (5, 3, 6)) (some (5, 3, 6))
    (.next ([510000000000], [1935000000000]) (some (5, 3, 6)) (some (5, 3, 6)) (.next ([0],
    [2760000000000]) (some (5, 3, 6)) (some (5, 3, 6)) (.next ([-165000000000], [6570000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-285000000000, 9000000000000], [4965000000000,
    -9000000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-555000000000], [4680000000000])
    (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-720000000000], [4845000000000]) (some (0, 3, 4))
    (some (0, 3, 4)) (.next ([-555000000000], [1920000000000]) (some (0, 3, 4)) (some (0, 3, 4))
    (.next ([-2445000000000], [7125000000000]) (some (0, 3, 4)) (some (1, 3, 4)) (.next
    ([-720000000000], [2085000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-2760000000000],
    [6615000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-2760000000000, 0], [4920000000000,
    9000000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-4455000000000, 9000000000000],
    [6615000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-4125000000000], [6060000000000])
    (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-4125000000000], [5895000000000]) (some (1, 3, 4))
    (some (1, 3, 4)) (.next ([-5205000000000], [7125000000000]) (some (1, 3, 4)) (some (1, 3, 4))
    (.next ([-4680000000000, 0], [6285000000000, 9000000000000]) (some (1, 3, 4)) (some (1, 3, 4))
    (.next ([-4845000000000, 0], [6285000000000, 9000000000000]) (some (1, 3, 4)) (some (1, 3, 4))
    (.next ([-1935000000000], [2445000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.terminal (some
    (1, 3, 4)) (some (1, 6, 4)) (some (1, 6, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan38Owner4Part0 : FanWitness := (.next ([1095000000000], [1785000000000]) (some (6, 1, 3))
    (some (6, 1, 3)) (.next ([2160000000000, 9000000000000], [4215000000000]) (some (6, 1, 3)) (some
    (6, 1, 3)) (.next ([555000000000], [1230000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([660000000000], [3495000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([720000000000],
    [4155000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([555000000000, 9000000000000],
    [4320000000000, -9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([660000000000],
    [5820000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([0, 9000000000000], [3090000000000,
    -9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([0], [4215000000000]) (some (6, 1,
    3)) (some (6, 1, 3)) (.next ([-1125000000000], [6375000000000]) (some (0, 1, 3)) (some (0, 1,
    3)) (.next ([-1605000000000], [6480000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-1080000000000], [3090000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1995000000000,
    9000000000000], [4875000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2160000000000],
    [5250000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2310000000000], [4875000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-4215000000000], [8385000000000]) (some (0, 1, 3))
    (some (0, 1, 6)) (.next ([-1785000000000], [2880000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-4215000000000], [6375000000000, 9000000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-1230000000000], [1785000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-3495000000000], [4155000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-4155000000000],
    [4875000000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-4320000000000, 9000000000000],
    [4875000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-5820000000000], [6480000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-3090000000000, 9000000000000], [3090000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.terminal (some (0, 2, 6)) (some (0, 2, 6)) (some (0, 2,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan39Owner4Part0 : FanWitness := (.next ([2160000000000, 9000000000000], [4215000000000]) (some
    (5, 1, 6)) (some (5, 1, 6)) (.next ([555000000000], [1230000000000]) (some (5, 1, 6)) (some (5,
    1, 6)) (.next ([660000000000], [3495000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
    ([720000000000], [4155000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([555000000000,
    9000000000000], [4320000000000, -9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
    ([660000000000], [5820000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, 9000000000000],
    [3090000000000, -9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0], [4215000000000])
    (some (5, 1, 6)) (some (5, 1, 6)) (.next ([-1125000000000], [6375000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-720000000000], [3030000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-1605000000000], [6480000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-705000000000], [2310000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-1995000000000,
    9000000000000], [4875000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2160000000000],
    [5250000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1935000000000], [4095000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-4215000000000], [7185000000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([-1785000000000], [2880000000000]) (some (0, 1, 3)) (some (0, 6, 3))
    (.next ([-4215000000000], [6375000000000, 9000000000000]) (some (0, 6, 3)) (some (0, 6, 3))
    (.next ([-1230000000000], [1785000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next
    ([-3495000000000], [4155000000000]) (some (0, 6, 3)) (some (0, 6, 4)) (.next ([-4155000000000],
    [4875000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-4320000000000, 9000000000000],
    [4875000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-5820000000000], [6480000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3090000000000, 9000000000000], [3090000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.terminal (some (0, 6, 4)) (some (0, 6, 5)) (some (0, 6,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan39Owner5Part0 : FanWitness := (.next ([7185000000000], [1815000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([375000000000], [105000000000]) (some (5, 1, 2)) (some (5, 1, 2))
    (.next ([255000000000, 9000000000000], [465000000000, -9000000000000]) (some (5, 1, 2)) (some
    (5, 1, 2)) (.next ([2250000000000], [4680000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([2160000000000, 9000000000000], [5505000000000, 0]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([720000000000], [1905000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1785000000000,
    9000000000000], [5400000000000, 0]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1785000000000],
    [6840000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1680000000000], [7320000000000])
    (some (5, 1, 2)) (some (5, 1, 2)) (.next ([345000000000, 9000000000000], [6840000000000,
    -9000000000000]) (some (5, 1, 2)) (some (5, 1, 5)) (.next ([90000000000], [6375000000000]) (some
    (0, 1, 5)) (some (0, 1, 5)) (.next ([0, 0], [2160000000000, 9000000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-375000000000], [5400000000000]) (some (0, 1, 5)) (some (0, 2, 5))
    (.next ([-1815000000000], [9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-105000000000], [480000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-465000000000,
    9000000000000], [720000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4680000000000],
    [6930000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5505000000000, 0], [7665000000000,
    9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1905000000000], [2625000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5400000000000, 0], [7185000000000, 9000000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-6840000000000], [8625000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-7320000000000], [9000000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-6840000000000, 9000000000000], [7185000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-6375000000000], [6465000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some
    (0, 2, 5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_1 : ExcludedOn (model32.B 1 ++ [step32.q]) 9000000000000 (model32.caps 1)
    (model32.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_2 : ExcludedOn (model32.B 2 ++ [step32.q]) 9000000000000 (model32.caps 2)
    (model32.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_3 : ExcludedOn (model32.B 3 ++ [step32.q]) 9000000000000 (model32.caps 3)
    (model32.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3525000000000], [225000000000]) (some (4, 1, 3))
      (some (5, 2, 3)) (.next ([4125000000000], [555000000000]) (some (5, 2, 3)) (some (5, 2, 3))
      (.next ([5910000000000, 9000000000000], [930000000000, -9000000000000]) (some (5, 2, 3)) (some
      (5, 2, 3)) (.next ([2160000000000], [375000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([4125000000000], [720000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([1995000000000],
      [375000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([1365000000000], [555000000000])
      (some (5, 2, 3)) (some (5, 6, 3)) (.next ([1365000000000], [720000000000]) (some (5, 6, 3))
      (some (5, 6, 3)) (.next ([3855000000000], [2760000000000]) (some (5, 6, 3)) (some (5, 6, 3))
      (.next ([3750000000000], [3090000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([2160000000000, 9000000000000], [2760000000000]) (some (5, 6, 3)) (some (5, 6, 3))
      fan32Owner3Part0)))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded32_5 : ExcludedOn (model32.B 5 ++ [step32.q]) 9000000000000 (model32.caps 5)
    (model32.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_6 : ExcludedOn (model32.B 6 ++ [step32.q]) 9000000000000 (model32.caps 6)
    (model32.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 3 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_1 : ExcludedOn (model33.B 1 ++ [step33.q]) 9000000000000 (model33.caps 1)
    (model33.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_3 : ExcludedOn (model33.B 3 ++ [step33.q]) 9000000000000 (model33.caps 3)
    (model33.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000], [555000000000]) (some (4, 1, 3))
      (some (5, 2, 3)) (.next ([4125000000000], [720000000000]) (some (5, 2, 3)) (some (5, 2, 3))
      (.next ([1365000000000], [555000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([1365000000000], [720000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([3855000000000],
      [2760000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([3375000000000], [2760000000000])
      (some (5, 2, 3)) (some (5, 2, 3)) (.next ([3375000000000], [3240000000000]) (some (5, 2, 3))
      (some (5, 2, 3)) fan33Owner3Part0)))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0
      1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_4 : ExcludedOn (model33.B 4 ++ [step33.q]) 9000000000000 (model33.caps 4)
    (model33.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 4 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

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
  apply ExclusionHint.sound (.witnessedFan (.next ([4635000000000], [240000000000]) (some (4, 1, 3))
      (some (5, 2, 3)) (.next ([4125000000000], [555000000000]) (some (5, 2, 3)) (some (5, 2, 3))
      (.next ([4125000000000], [720000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([1365000000000], [555000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([1740000000000],
      [780000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([1365000000000], [720000000000])
      (some (5, 2, 3)) (some (5, 2, 3)) (.next ([4680000000000, 9000000000000], [2715000000000,
      -9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([2715000000000], [1605000000000])
      (some (5, 2, 3)) (some (5, 2, 3)) (.next ([2550000000000], [1605000000000]) (some (5, 2, 3))
      (some (5, 2, 3)) (.next ([3855000000000], [2760000000000]) (some (5, 2, 3)) (some (5, 6, 3))
      (.next ([2160000000000, 9000000000000], [2760000000000]) (some (5, 6, 3)) (some (5, 6, 3))
      fan34Owner3Part0)))))))))))) (den :=
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
  apply ExclusionHint.sound (.pair 3 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_1 : ExcludedOn (model35.B 1 ++ [step35.q]) 9000000000000 (model35.caps 1)
    (model35.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_3 : ExcludedOn (model35.B 3 ++ [step35.q]) 9000000000000 (model35.caps 3)
    (model35.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5112000000000], [273000000000]) (some (4, 1, 3))
      (some (5, 2, 3)) (.next ([4125000000000], [555000000000]) (some (5, 2, 3)) (some (5, 2, 3))
      (.next ([2487000000000, 0], [465000000000, -9000000000000]) (some (5, 2, 3)) (some (5, 2, 3))
      (.next ([1365000000000], [555000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([4557000000000], [2193000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([1365000000000],
      [720000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([4392000000000], [2358000000000])
      (some (5, 2, 3)) (some (5, 2, 3)) (.next ([2625000000000], [1503000000000]) (some (5, 2, 3))
      (some (5, 2, 3)) (.next ([3855000000000], [2760000000000]) (some (5, 2, 3)) (some (5, 2, 6))
      fan35Owner3Part0)))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_4 : ExcludedOn (model35.B 4 ++ [step35.q]) 9000000000000 (model35.caps 4)
    (model35.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 3 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_1 : ExcludedOn (model36.B 1 ++ [step36.q]) 9000000000000 (model36.caps 1)
    (model36.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_3 : ExcludedOn (model36.B 3 ++ [step36.q]) 9000000000000 (model36.caps 3)
    (model36.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000, 0], [225000000000,
      -9000000000000]) (some (4, 1, 3)) (some (5, 2, 3)) (.next ([4125000000000], [555000000000])
      (some (5, 2, 3)) (some (5, 2, 3)) (.next ([4125000000000], [720000000000]) (some (5, 2, 3))
      (some (5, 2, 3)) (.next ([5205000000000], [1305000000000]) (some (5, 2, 3)) (some (5, 2, 3))
      (.next ([5040000000000], [1470000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([2385000000000], [855000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([1365000000000],
      [555000000000]) (some (5, 2, 3)) (some (5, 2, 6)) (.next ([1365000000000], [720000000000])
      (some (5, 2, 6)) (some (5, 2, 6)) (.next ([3375000000000], [2385000000000]) (some (5, 2, 6))
      (some (5, 2, 6)) (.next ([3855000000000], [2760000000000]) (some (5, 2, 6)) (some (5, 2, 6))
      (.next ([2160000000000, 9000000000000], [2760000000000]) (some (5, 2, 6)) (some (5, 2, 6))
      fan36Owner3Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded36_4 : ExcludedOn (model36.B 4 ++ [step36.q]) 9000000000000 (model36.caps 4)
    (model36.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_6 : ExcludedOn (model36.B 6 ++ [step36.q]) 9000000000000 (model36.caps 6)
    (model36.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_7 : ExcludedOn (model36.B 7 ++ [step36.q]) 9000000000000 (model36.caps 7)
    (model36.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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

theorem excluded37_0 : ExcludedOn (model37.B 0 ++ [step37.q]) 9000000000000 (model37.caps 0)
    (model37.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_1 : ExcludedOn (model37.B 1 ++ [step37.q]) 9000000000000 (model37.caps 1)
    (model37.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_3 : ExcludedOn (model37.B 3 ++ [step37.q]) 9000000000000 (model37.caps 3)
    (model37.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6405000000000], [165000000000]) (some (4, 1, 6))
      (some (5, 2, 6)) (.next ([4680000000000, 0], [285000000000, -9000000000000]) (some (5, 2, 6))
      (some (5, 2, 6)) (.next ([4125000000000], [555000000000]) (some (5, 2, 6)) (some (5, 2, 6))
      (.next ([4125000000000], [720000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next
      ([1365000000000], [555000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([4680000000000],
      [2445000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([1365000000000], [720000000000])
      (some (5, 2, 6)) (some (5, 2, 6)) (.next ([3855000000000], [2760000000000]) (some (5, 2, 6))
      (some (5, 2, 6)) (.next ([2160000000000, 9000000000000], [2760000000000]) (some (5, 2, 6))
      (some (5, 2, 6)) fan37Owner3Part0)))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel)
      0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_4 : ExcludedOn (model37.B 4 ++ [step37.q]) 9000000000000 (model37.caps 4)
    (model37.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_5 : ExcludedOn (model37.B 5 ++ [step37.q]) 9000000000000 (model37.caps 5)
    (model37.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_6 : ExcludedOn (model37.B 6 ++ [step37.q]) 9000000000000 (model37.caps 6)
    (model37.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_7 : ExcludedOn (model37.B 7 ++ [step37.q]) 9000000000000 (model37.caps 7)
    (model37.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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

theorem excluded38_0 : ExcludedOn (model38.B 0 ++ [step38.q]) 9000000000000 (model38.caps 0)
    (model38.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_1 : ExcludedOn (model38.B 1 ++ [step38.q]) 9000000000000 (model38.caps 1)
    (model38.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_2 : ExcludedOn (model38.B 2 ++ [step38.q]) 9000000000000 (model38.caps 2)
    (model38.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_4 : ExcludedOn (model38.B 4 ++ [step38.q]) 9000000000000 (model38.caps 4)
    (model38.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5250000000000], [1125000000000]) (some (6, 0,
      2)) (some (6, 1, 3)) (.next ([4875000000000], [1605000000000]) (some (6, 1, 3)) (some (6, 1,
      3)) (.next ([2010000000000], [1080000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
      ([2880000000000, 9000000000000], [1995000000000, -9000000000000]) (some (6, 1, 3)) (some (6,
      1, 3)) (.next ([3090000000000], [2160000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
      ([2565000000000], [2310000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4170000000000],
      [4215000000000]) (some (6, 1, 3)) (some (6, 1, 3)) fan38Owner4Part0)))))))) (den :=
      9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_8 : ExcludedOn (model38.B 8 ++ [step38.q]) 9000000000000 (model38.caps 8)
    (model38.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3075000000000], [1755000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([4830000000000], [4170000000000]) (some (0, 1, 2)) (some (0, 1,
      2)) (.next ([2475000000000], [4770000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([60000000000], [4170000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [4770000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.next ([-1755000000000], [4830000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-4170000000000], [9000000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-4770000000000], [7245000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-4170000000000], [4230000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded38_2
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_2 : ExcludedOn (model39.B 2 ++ [step39.q]) 9000000000000 (model39.caps 2)
    (model39.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_3 : ExcludedOn (model39.B 3 ++ [step39.q]) 9000000000000 (model39.caps 3)
    (model39.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1815000000000], [570000000000]) (some (2, 0, 4))
      (some (3, 0, 4)) (.next ([4170000000000], [3015000000000]) (some (3, 0, 1)) (some (3, 0, 1))
      (.next ([3975000000000, 9000000000000], [5025000000000, -9000000000000]) (some (3, 0, 1))
      (some (3, 4, 1)) (.next ([2160000000000, 9000000000000], [4455000000000, -9000000000000])
      (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2160000000000, 9000000000000], [4830000000000])
      (some (3, 4, 1)) (some (3, 4, 2)) (.next ([1785000000000], [4830000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([1815000000000], [7185000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([0], [4830000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-570000000000],
      [2385000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-3015000000000], [7185000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-5025000000000, 9000000000000], [9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4455000000000, 9000000000000], [6615000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4830000000000, 0], [6990000000000, 9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4830000000000], [6615000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-7185000000000], [9000000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded39_4 : ExcludedOn (model39.B 4 ++ [step39.q]) 9000000000000 (model39.caps 4)
    (model39.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5250000000000], [1125000000000]) (some (5, 0,
      6)) (some (5, 1, 6)) (.next ([2310000000000], [720000000000]) (some (5, 1, 6)) (some (5, 1,
      6)) (.next ([4875000000000], [1605000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([1605000000000], [705000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2880000000000,
      9000000000000], [1995000000000, -9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([3090000000000], [2160000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2160000000000],
      [1935000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2970000000000], [4215000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1095000000000], [1785000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) fan39Owner4Part0)))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded39_5 : ExcludedOn (model39.B 5 ++ [step39.q]) 9000000000000 (model39.caps 5)
    (model39.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5025000000000], [375000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) fan39Owner5Part0)) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100
      (by decide +kernel)
  decide +kernel

theorem excluded39_6 : ExcludedOn (model39.B 6 ++ [step39.q]) 9000000000000 (model39.caps 6)
    (model39.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_7 : ExcludedOn (model39.B 7 ++ [step39.q]) 9000000000000 (model39.caps 7)
    (model39.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

end Sext240000250000
end ConwaySoifer.Simplified.Certificates
