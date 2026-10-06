/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext255000260000
import Mathlib.Tactic.FinCases

/-!
# Sext 255000 260000 2

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
namespace Sext255000260000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part0 : FanWitness := (.next ([-1147500000000], [5737500000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-397500000000], [1920000000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-1537500000000], [7162500000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1522500000000], [6712500000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1522500000000], [6315000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1147500000000], [4215000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1912500000000], [6787500000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1522500000000], [5362500000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1912500000000], [6390000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1522500000000], [4965000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-750000000000],
    [2295000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-4965000000000], [10155000000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-375000000000], [750000000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-5355000000000], [10230000000000]) (some (10, 3, 6)) (some (10, 3,
    7)) (.next ([-772500000000], [1147500000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next
    ([-1522500000000], [1920000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-315000000000],
    [390000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-5167500000000], [5940000000000])
    (some (10, 3, 7)) (some (10, 4, 7)) (.next ([-5565000000000], [6337500000000]) (some (10, 4, 7))
    (some (10, 4, 7)) (.next ([-3442500000000], [3840000000000]) (some (10, 4, 7)) (some (10, 4, 7))
    (.next ([-5242500000000], [5625000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-5640000000000], [6022500000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-6315000000000], [6712500000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-6390000000000], [6397500000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.terminal (some (10, 4,
    7)) (some (10, 4, 7)) (some (10, 4, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part1 : FanWitness := (.next ([3840000000000], [1522500000000]) (some (8, 10, 4))
    (some (8, 10, 4)) (.next ([4477500000000], [1912500000000]) (some (8, 10, 4)) (some (8, 10, 4))
    (.next ([3442500000000], [1522500000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
    ([1545000000000], [750000000000]) (some (8, 10, 4)) (some (10, 10, 4)) (.next ([5190000000000],
    [4965000000000]) (some (10, 10, 4)) (some (10, 10, 4)) (.next ([375000000000], [375000000000])
    (some (10, 3, 4)) (some (10, 3, 4)) (.next ([4875000000000], [5355000000000]) (some (10, 3, 4))
    (some (10, 3, 4)) (.next ([375000000000], [772500000000]) (some (10, 3, 4)) (some (10, 3, 4))
    (.next ([397500000000], [1522500000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next
    ([75000000000], [315000000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([772500000000],
    [5167500000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([772500000000], [5565000000000])
    (some (10, 3, 4)) (some (10, 3, 4)) (.next ([397500000000], [3442500000000]) (some (10, 3, 4))
    (some (10, 3, 4)) (.next ([382500000000], [5242500000000]) (some (10, 3, 4)) (some (10, 3, 4))
    (.next ([382500000000], [5640000000000]) (some (10, 3, 4)) (some (10, 3, 5)) (.next
    ([397500000000], [6315000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([7500000000],
    [6390000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([0], [1920000000000]) (some (10, 3,
    5)) (some (10, 3, 5)) (.next ([-390000000000], [6787500000000]) (some (10, 3, 5)) (some (10, 3,
    6)) (.next ([-750000000000], [7087500000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-750000000000], [5737500000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-1140000000000],
    [7162500000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-1147500000000], [7087500000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-750000000000], [3817500000000]) (some (10, 3, 6))
    (some (10, 3, 6)) fan20Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner0Part0 : FanWitness := (.next ([-1147500000000], [7087500000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-772500000000], [4528500000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-772500000000], [4131000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-397500000000], [1920000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-1537500000000],
    [7162500000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-1522500000000], [6712500000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-1522500000000], [6315000000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-1912500000000], [6787500000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-1912500000000], [6390000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-750000000000], [2295000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-4131000000000],
    [10071000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-4521000000000],
    [10146000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-375000000000], [750000000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-772500000000], [1147500000000]) (some (10, 3, 6))
    (some (10, 3, 7)) (.next ([-2608500000000], [3756000000000]) (some (10, 3, 7)) (some (10, 3, 7))
    (.next ([-2608500000000], [3358500000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next
    ([-1522500000000], [1920000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-315000000000],
    [390000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-5167500000000], [5940000000000])
    (some (10, 3, 7)) (some (10, 4, 7)) (.next ([-5565000000000], [6337500000000]) (some (10, 4, 7))
    (some (10, 4, 7)) (.next ([-5242500000000], [5625000000000]) (some (10, 4, 7)) (some (10, 4, 7))
    (.next ([-5640000000000], [6022500000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-6315000000000], [6712500000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-6390000000000], [6397500000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.terminal (some (10, 4,
    7)) (some (10, 4, 7)) (some (10, 4, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner0Part1 : FanWitness := (.next ([4792500000000], [1522500000000]) (some (10, 10, 4))
    (some (10, 10, 4)) (.next ([4875000000000], [1912500000000]) (some (10, 10, 4)) (some (10, 10,
    4)) (.next ([4477500000000], [1912500000000]) (some (10, 10, 4)) (some (10, 10, 4)) (.next
    ([1545000000000], [750000000000]) (some (10, 10, 4)) (some (10, 10, 4)) (.next ([5940000000000],
    [4131000000000]) (some (10, 10, 4)) (some (10, 10, 4)) (.next ([5625000000000], [4521000000000])
    (some (10, 3, 4)) (some (10, 3, 4)) (.next ([375000000000], [375000000000]) (some (10, 3, 4))
    (some (10, 3, 4)) (.next ([375000000000], [772500000000]) (some (10, 3, 4)) (some (10, 3, 4))
    (.next ([1147500000000], [2608500000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next
    ([750000000000], [2608500000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([397500000000],
    [1522500000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([75000000000], [315000000000])
    (some (10, 3, 4)) (some (10, 3, 4)) (.next ([772500000000], [5167500000000]) (some (10, 3, 4))
    (some (10, 3, 4)) (.next ([772500000000], [5565000000000]) (some (10, 3, 4)) (some (10, 3, 4))
    (.next ([382500000000], [5242500000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next
    ([382500000000], [5640000000000]) (some (10, 3, 4)) (some (10, 3, 5)) (.next ([397500000000],
    [6315000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([7500000000], [6390000000000])
    (some (10, 3, 5)) (some (10, 3, 5)) (.next ([0], [1920000000000]) (some (10, 3, 5)) (some (10,
    3, 5)) (.next ([-390000000000], [6787500000000]) (some (10, 3, 5)) (some (10, 3, 6)) (.next
    ([-397500000000], [4903500000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-750000000000],
    [7087500000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-397500000000], [3381000000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-1140000000000], [7162500000000]) (some (10, 3, 6))
    (some (10, 3, 6)) fan21Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner4Part0 : FanWitness := (.next ([-2295000000000], [5295000000000]) (some (8, 1, 4))
    (some (8, 1, 4)) (.next ([-4410000000000], [9090000000000]) (some (8, 1, 4)) (some (8, 1, 4))
    (.next ([-738000000000], [1500000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next
    ([-2295000000000, -9000000000000], [4305000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next
    ([-1410000000000], [2557500000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([-5244000000000],
    [9174000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([-448500000000], [756000000000])
    (some (8, 1, 4)) (some (8, 1, 4)) (.next ([-2949000000000, 9000000000000], [4869000000000])
    (some (8, 1, 4)) (some (8, 1, 5)) (.next ([-711000000000], [1131000000000]) (some (8, 1, 5))
    (some (8, 1, 5)) (.next ([-4080000000000], [6375000000000, 9000000000000]) (some (8, 1, 5))
    (some (8, 1, 5)) (.next ([-1785000000000], [2670000000000]) (some (8, 1, 5)) (some (8, 1, 5))
    (.next ([-262500000000], [375000000000]) (some (8, 1, 5)) (some (8, 1, 5)) (.next
    ([-6006000000000], [8436000000000]) (some (8, 1, 5)) (some (8, 1, 6)) (.next ([-5557500000000],
    [7680000000000]) (some (8, 1, 6)) (some (8, 1, 6)) (.next ([-5295000000000], [7305000000000])
    (some (8, 1, 6)) (some (8, 1, 6)) (.next ([-1494000000000], [1807500000000]) (some (8, 1, 6))
    (some (8, 1, 8)) (.next ([-3705000000000], [4410000000000]) (some (8, 1, 8)) (some (8, 1, 8))
    (.next ([-4455000000000], [5244000000000]) (some (8, 1, 8)) (some (8, 2, 8)) (.next
    ([-3711000000000, 9000000000000], [4131000000000]) (some (8, 2, 8)) (some (8, 2, 8)) (.next
    ([-750000000000], [834000000000]) (some (8, 2, 8)) (some (8, 2, 8)) (.next ([-4410000000000],
    [4785000000000]) (some (8, 2, 8)) (some (8, 3, 8)) (.next ([-3262500000000, 9000000000000],
    [3375000000000]) (some (8, 3, 8)) (some (8, 3, 8)) (.next ([-1869000000000], [1920000000000])
    (some (8, 3, 8)) (some (8, 3, 8)) (.next ([-5955000000000], [6006000000000]) (some (8, 3, 8))
    (some (8, 3, 8)) (.terminal (some (8, 3, 8)) (some (0, 3, 8)) (some (8, 3,
    8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner4Part1 : FanWitness := (.next ([1920000000000, 9000000000000], [2949000000000,
    -9000000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([420000000000], [711000000000]) (some
    (8, 1, 4)) (some (8, 1, 4)) (.next ([2295000000000, 9000000000000], [4080000000000]) (some (8,
    1, 4)) (some (8, 1, 4)) (.next ([885000000000], [1785000000000]) (some (8, 1, 4)) (some (8, 1,
    4)) (.next ([112500000000], [262500000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next
    ([2430000000000], [6006000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([2122500000000],
    [5557500000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([2010000000000], [5295000000000])
    (some (8, 1, 4)) (some (8, 1, 4)) (.next ([313500000000], [1494000000000]) (some (8, 1, 4))
    (some (8, 1, 4)) (.next ([705000000000], [3705000000000]) (some (8, 1, 4)) (some (8, 1, 4))
    (.next ([789000000000], [4455000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next
    ([420000000000, 9000000000000], [3711000000000, -9000000000000]) (some (8, 1, 4)) (some (8, 1,
    4)) (.next ([84000000000], [750000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next
    ([375000000000], [4410000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([112500000000,
    9000000000000], [3262500000000, -9000000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next
    ([51000000000], [1869000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([51000000000],
    [5955000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([0], [4080000000000]) (some (8, 1,
    4)) (some (8, 1, 4)) (.next ([-375000000000], [5244000000000]) (some (8, 1, 4)) (some (8, 1, 4))
    (.next ([-705000000000], [6262500000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next
    ([-1080000000000], [6375000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([-654000000000],
    [2250000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([-1875000000000], [6006000000000])
    (some (8, 1, 4)) (some (8, 1, 4)) (.next ([-2182500000000], [5557500000000]) (some (8, 1, 4))
    (some (8, 1, 4)) fan22Owner4Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner4Part0 : FanWitness := (.next ([-2961000000000], [8211000000000]) (some (0, 1, 8))
    (some (0, 1, 8)) (.next ([-2182500000000], [5557500000000]) (some (0, 1, 8)) (some (0, 1, 8))
    (.next ([-2295000000000], [5295000000000]) (some (0, 1, 8)) (some (0, 1, 8)) (.next
    ([-738000000000], [1500000000000]) (some (0, 1, 8)) (some (0, 1, 8)) (.next ([-1410000000000],
    [2557500000000]) (some (0, 1, 8)) (some (0, 1, 8)) (.next ([-448500000000], [756000000000])
    (some (0, 1, 8)) (some (0, 1, 8)) (.next ([-2949000000000, 9000000000000], [4869000000000])
    (some (0, 1, 8)) (some (0, 1, 8)) (.next ([-1836000000000, 9000000000000], [2955000000000,
    -9000000000000]) (some (0, 1, 8)) (some (0, 1, 8)) (.next ([-711000000000], [1131000000000])
    (some (0, 1, 8)) (some (0, 1, 8)) (.next ([-4080000000000], [6375000000000, 9000000000000])
    (some (0, 1, 8)) (some (0, 1, 8)) (.next ([-1785000000000], [2670000000000]) (some (0, 1, 8))
    (some (0, 1, 8)) (.next ([-262500000000], [375000000000]) (some (0, 1, 8)) (some (0, 1, 8))
    (.next ([-4131000000000], [5250000000000]) (some (0, 1, 8)) (some (0, 1, 8)) (.next
    ([-3666000000000], [4506000000000]) (some (0, 1, 8)) (some (0, 1, 8)) (.next ([-1494000000000],
    [1807500000000]) (some (0, 1, 8)) (some (0, 1, 8)) (.next ([-3705000000000], [4410000000000])
    (some (0, 1, 8)) (some (0, 1, 8)) (.next ([-4455000000000], [5244000000000]) (some (0, 1, 8))
    (some (0, 2, 8)) (.next ([-3711000000000, 9000000000000], [4131000000000]) (some (0, 2, 8))
    (some (0, 2, 8)) (.next ([-750000000000], [834000000000]) (some (0, 2, 8)) (some (0, 2, 8))
    (.next ([-4410000000000], [4785000000000]) (some (0, 2, 8)) (some (0, 3, 8)) (.next
    ([-3262500000000, 9000000000000], [3375000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next
    ([-1869000000000], [1920000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-5955000000000],
    [6006000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-3750000000000], [3756000000000])
    (some (0, 3, 8)) (some (0, 3, 8)) (.terminal (some (0, 3, 8)) (some (0, 3, 8)) (some (0, 3,
    8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner4Part1 : FanWitness := (.next ([2295000000000, 9000000000000], [4080000000000]) (some
    (7, 1, 4)) (some (7, 1, 4)) (.next ([885000000000], [1785000000000]) (some (7, 1, 4)) (some (7,
    1, 4)) (.next ([112500000000], [262500000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
    ([1119000000000], [4131000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([840000000000],
    [3666000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([313500000000], [1494000000000])
    (some (7, 1, 4)) (some (7, 1, 4)) (.next ([705000000000], [3705000000000]) (some (7, 1, 4))
    (some (7, 1, 4)) (.next ([789000000000], [4455000000000]) (some (7, 1, 4)) (some (7, 1, 4))
    (.next ([420000000000, 9000000000000], [3711000000000, -9000000000000]) (some (7, 1, 4)) (some
    (7, 1, 4)) (.next ([84000000000], [750000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
    ([375000000000], [4410000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([112500000000,
    9000000000000], [3262500000000, -9000000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
    ([51000000000], [1869000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([51000000000],
    [5955000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([6000000000], [3750000000000]) (some
    (7, 1, 4)) (some (7, 1, 4)) (.next ([0], [4080000000000]) (some (7, 1, 4)) (some (7, 1, 4))
    (.next ([-45000000000], [1881000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
    ([-375000000000], [5244000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-705000000000],
    [6262500000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-307500000000], [2256000000000])
    (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-1080000000000], [6375000000000]) (some (0, 1, 4))
    (some (0, 1, 4)) (.next ([-756000000000], [3012000000000]) (some (0, 1, 4)) (some (0, 1, 4))
    (.next ([-654000000000], [2250000000000]) (some (0, 1, 4)) (some (0, 1, 8)) (.next
    ([-1875000000000], [6006000000000]) (some (0, 1, 8)) (some (0, 1, 8))
    fan23Owner4Part0))))))))))))))))))))))))

theorem excluded16_0 : ExcludedOn (model16.B 0 ++ [step16.q]) 9000000000000 (model16.caps 0)
    (model16.ord 0) 0 1 200 := by
  apply ExclusionHint.sound (.pair 3 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded16_1 : ExcludedOn (model16.B 1 ++ [step16.q]) 9000000000000 (model16.caps 1)
    (model16.ord 1) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded16_2 : ExcludedOn (model16.B 2 ++ [step16.q]) 9000000000000 (model16.caps 2)
    (model16.ord 2) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded16_3 : ExcludedOn (model16.B 3 ++ [step16.q]) 9000000000000 (model16.caps 3)
    (model16.ord 3) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3570000000000], [135000000000]) (some (2, 4, 1))
      (some (3, 4, 1)) (.next ([6000000000000, 9000000000000], [705000000000, -9000000000000]) (some
      (3, 4, 1)) (some (3, 4, 1)) (.next ([4275000000000, -9000000000000], [2295000000000,
      9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([3705000000000], [3000000000000])
      (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2295000000000, 9000000000000], [2295000000000,
      9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2295000000000, 9000000000000],
      [4275000000000, -9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([1410000000000,
      -9000000000000], [3000000000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next ([0],
      [2295000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-135000000000],
      [3705000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-705000000000, 9000000000000],
      [6705000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2295000000000, -9000000000000],
      [6570000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3000000000000], [6705000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2295000000000, -9000000000000], [4590000000000,
      18000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4275000000000, 9000000000000],
      [6570000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3000000000000], [4410000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (4, 1,
      2)) (some (4, 1, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded16_5 : ExcludedOn (model16.B 5 ++ [step16.q]) 9000000000000 (model16.caps 5)
    (model16.ord 5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded16_6 : ExcludedOn (model16.B 6 ++ [step16.q]) 9000000000000 (model16.caps 6)
    (model16.ord 6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded16_7 : ExcludedOn (model16.B 7 ++ [step16.q]) 9000000000000 (model16.caps 7)
    (model16.ord 7) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded16_8 : ExcludedOn (model16.B 8 ++ [step16.q]) 9000000000000 (model16.caps 8)
    (model16.ord 8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded16_9 : ExcludedOn (model16.B 9 ++ [step16.q]) 9000000000000 (model16.caps 9)
    (model16.ord 9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked16 : StepValid model16 9000000000000 step16 0 1 200 := by
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
    · exact (hj rfl).elim
    · exact excluded16_5
    · exact excluded16_6
    · exact excluded16_7
    · exact excluded16_8
    · exact excluded16_9
theorem next16 : model16.insert step16 = model17 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded17_0 : ExcludedOn (model17.B 0 ++ [step17.q]) 9000000000000 (model17.caps 0)
    (model17.ord 0) 0 1 200 := by
  apply ExclusionHint.sound (.pair 3 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded17_1 : ExcludedOn (model17.B 1 ++ [step17.q]) 9000000000000 (model17.caps 1)
    (model17.ord 1) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded17_2 : ExcludedOn (model17.B 2 ++ [step17.q]) 9000000000000 (model17.caps 2)
    (model17.ord 2) 0 1 200 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded17_3 : ExcludedOn (model17.B 3 ++ [step17.q]) 9000000000000 (model17.caps 3)
    (model17.ord 3) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3195000000000], [247500000000]) (some (2, 4, 1))
      (some (3, 4, 1)) (.next ([5737500000000, 9000000000000], [1080000000000, -9000000000000])
      (some (3, 4, 1)) (some (3, 4, 1)) (.next ([4275000000000, -9000000000000], [2295000000000,
      9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([3442500000000], [3375000000000])
      (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2295000000000, 9000000000000], [2295000000000,
      9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2295000000000, 9000000000000],
      [4275000000000, -9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([1147500000000,
      -9000000000000], [3375000000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next ([0],
      [2295000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-247500000000],
      [3442500000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1080000000000, 9000000000000],
      [6817500000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2295000000000, -9000000000000],
      [6570000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3375000000000], [6817500000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2295000000000, -9000000000000], [4590000000000,
      18000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4275000000000, 9000000000000],
      [6570000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3375000000000], [4522500000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (4, 1,
      2)) (some (4, 1, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded17_5 : ExcludedOn (model17.B 5 ++ [step17.q]) 9000000000000 (model17.caps 5)
    (model17.ord 5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded17_6 : ExcludedOn (model17.B 6 ++ [step17.q]) 9000000000000 (model17.caps 6)
    (model17.ord 6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded17_7 : ExcludedOn (model17.B 7 ++ [step17.q]) 9000000000000 (model17.caps 7)
    (model17.ord 7) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded17_8 : ExcludedOn (model17.B 8 ++ [step17.q]) 9000000000000 (model17.caps 8)
    (model17.ord 8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded17_9 : ExcludedOn (model17.B 9 ++ [step17.q]) 9000000000000 (model17.caps 9)
    (model17.ord 9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked17 : StepValid model17 9000000000000 step17 0 1 200 := by
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
    (model18.ord 0) 0 1 200 := by
  apply ExclusionHint.sound (.pair 3 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded18_1 : ExcludedOn (model18.B 1 ++ [step18.q]) 9000000000000 (model18.caps 1)
    (model18.ord 1) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded18_2 : ExcludedOn (model18.B 2 ++ [step18.q]) 9000000000000 (model18.caps 2)
    (model18.ord 2) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded18_3 : ExcludedOn (model18.B 3 ++ [step18.q]) 9000000000000 (model18.caps 3)
    (model18.ord 3) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded18_5 : ExcludedOn (model18.B 5 ++ [step18.q]) 9000000000000 (model18.caps 5)
    (model18.ord 5) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4770000000000], [480000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([480000000000], [90000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([4920000000000], [5340000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([4440000000000], [5250000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2295000000000,
      9000000000000], [5340000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1815000000000,
      9000000000000], [5250000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0, 0],
      [2295000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-480000000000],
      [5250000000000]) (some (4, 1, 2)) (some (4, 2, 2)) (.next ([-90000000000], [570000000000])
      (some (4, 2, 2)) (some (4, 2, 2)) (.next ([-5340000000000], [10260000000000]) (some (4, 2, 2))
      (some (4, 2, 3)) (.next ([-5250000000000], [9690000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([-5340000000000, 0], [7635000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 4))
      (.next ([-5250000000000, 0], [7065000000000, 9000000000000]) (some (4, 2, 4)) (some (4, 2, 4))
      (.terminal (some (4, 2, 4)) (some (0, 2, 4)) (some (4, 2, 4))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded18_6 : ExcludedOn (model18.B 6 ++ [step18.q]) 9000000000000 (model18.caps 6)
    (model18.ord 6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded18_7 : ExcludedOn (model18.B 7 ++ [step18.q]) 9000000000000 (model18.caps 7)
    (model18.ord 7) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded18_8 : ExcludedOn (model18.B 8 ++ [step18.q]) 9000000000000 (model18.caps 8)
    (model18.ord 8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded18_9 : ExcludedOn (model18.B 9 ++ [step18.q]) 9000000000000 (model18.caps 9)
    (model18.ord 9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked18 : StepValid model18 9000000000000 step18 0 1 200 := by
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
    · exact (hj rfl).elim
    · exact excluded18_5
    · exact excluded18_6
    · exact excluded18_7
    · exact excluded18_8
    · exact excluded18_9
theorem next18 : model18.insert step18 = model19 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded19_0 : ExcludedOn (model19.B 0 ++ [step19.q]) 9000000000000 (model19.caps 0)
    (model19.ord 0) 0 1 200 := by
  apply ExclusionHint.sound (.pair 3 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded19_1 : ExcludedOn (model19.B 1 ++ [step19.q]) 9000000000000 (model19.caps 1)
    (model19.ord 1) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded19_2 : ExcludedOn (model19.B 2 ++ [step19.q]) 9000000000000 (model19.caps 2)
    (model19.ord 2) 0 1 200 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded19_3 : ExcludedOn (model19.B 3 ++ [step19.q]) 9000000000000 (model19.caps 3)
    (model19.ord 3) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2439000000000], [555000000000]) (some (2, 4, 1))
      (some (3, 4, 1)) (.next ([5289000000000, 9000000000000], [1836000000000, -9000000000000])
      (some (3, 4, 1)) (some (3, 4, 1)) (.next ([4275000000000, -9000000000000], [2295000000000,
      9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2295000000000, 9000000000000],
      [2295000000000, 9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2994000000000],
      [4131000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2295000000000, 9000000000000],
      [4275000000000, -9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([699000000000,
      -9000000000000], [4131000000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next ([0],
      [2295000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-555000000000],
      [2994000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1836000000000, 9000000000000],
      [7125000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2295000000000, -9000000000000],
      [6570000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2295000000000, -9000000000000],
      [4590000000000, 18000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4131000000000],
      [7125000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4275000000000, 9000000000000],
      [6570000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4131000000000], [4830000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (4, 1,
      2)) (some (4, 1, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded19_5 : ExcludedOn (model19.B 5 ++ [step19.q]) 9000000000000 (model19.caps 5)
    (model19.ord 5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded19_6 : ExcludedOn (model19.B 6 ++ [step19.q]) 9000000000000 (model19.caps 6)
    (model19.ord 6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded19_7 : ExcludedOn (model19.B 7 ++ [step19.q]) 9000000000000 (model19.caps 7)
    (model19.ord 7) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded19_8 : ExcludedOn (model19.B 8 ++ [step19.q]) 9000000000000 (model19.caps 8)
    (model19.ord 8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded19_9 : ExcludedOn (model19.B 9 ++ [step19.q]) 9000000000000 (model19.caps 9)
    (model19.ord 9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked19 : StepValid model19 9000000000000 step19 0 1 200 := by
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
    · exact (hj rfl).elim
    · exact excluded19_5
    · exact excluded19_6
    · exact excluded19_7
    · exact excluded19_8
    · exact excluded19_9
theorem next19 : model19.insert step19 = model20 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded20_0 : ExcludedOn (model20.B 0 ++ [step20.q]) 9000000000000 (model20.caps 0)
    (model20.ord 0) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6397500000000], [390000000000]) (some (7, 10,
      4)) (some (8, 10, 4)) (.next ([6337500000000], [750000000000]) (some (8, 10, 4)) (some (8, 10,
      4)) (.next ([4987500000000], [750000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([6022500000000], [1140000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([5940000000000], [1147500000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([3067500000000], [750000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([4590000000000],
      [1147500000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([1522500000000], [397500000000])
      (some (8, 10, 4)) (some (8, 10, 4)) (.next ([5625000000000], [1537500000000]) (some (8, 10,
      4)) (some (8, 10, 4)) (.next ([5190000000000], [1522500000000]) (some (8, 10, 4)) (some (8,
      10, 4)) (.next ([4792500000000], [1522500000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([3067500000000], [1147500000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([4875000000000], [1912500000000]) (some (8, 10, 4)) (some (8, 10, 4))
      fan20Owner0Part1)))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded20_2 : ExcludedOn (model20.B 2 ++ [step20.q]) 9000000000000 (model20.caps 2)
    (model20.ord 2) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded20_3 : ExcludedOn (model20.B 3 ++ [step20.q]) 9000000000000 (model20.caps 3)
    (model20.ord 3) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6885000000000, 9000000000000], [2490000000000,
      -9000000000000]) (some (2, 4, 1)) (some (3, 4, 1)) (.next ([4275000000000, -9000000000000],
      [2295000000000, 9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2295000000000,
      9000000000000], [2295000000000, 9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next
      ([4590000000000], [4785000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([1785000000000],
      [2805000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2295000000000, 9000000000000],
      [4275000000000, -9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2295000000000,
      -9000000000000], [4785000000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next ([0],
      [2295000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-2490000000000,
      9000000000000], [9375000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2295000000000,
      -9000000000000], [6570000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2295000000000,
      -9000000000000], [4590000000000, 18000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-4785000000000], [9375000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-2805000000000], [4590000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4275000000000,
      9000000000000], [6570000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4785000000000],
      [7080000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2))
      (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded20_5 : ExcludedOn (model20.B 5 ++ [step20.q]) 9000000000000 (model20.caps 5)
    (model20.ord 5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded20_6 : ExcludedOn (model20.B 6 ++ [step20.q]) 9000000000000 (model20.caps 6)
    (model20.ord 6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded20_7 : ExcludedOn (model20.B 7 ++ [step20.q]) 9000000000000 (model20.caps 7)
    (model20.ord 7) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded20_8 : ExcludedOn (model20.B 8 ++ [step20.q]) 9000000000000 (model20.caps 8)
    (model20.ord 8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded20_9 : ExcludedOn (model20.B 9 ++ [step20.q]) 9000000000000 (model20.caps 9)
    (model20.ord 9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked20 : StepValid model20 9000000000000 step20 0 1 200 := by
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
    · exact (hj rfl).elim
    · exact excluded20_5
    · exact excluded20_6
    · exact excluded20_7
    · exact excluded20_8
    · exact excluded20_9
theorem next20 : model20.insert step20 = model21 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded21_0 : ExcludedOn (model21.B 0 ++ [step21.q]) 9000000000000 (model21.caps 0)
    (model21.ord 0) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6397500000000], [390000000000]) (some (7, 10,
      4)) (some (8, 10, 4)) (.next ([4506000000000], [397500000000]) (some (8, 10, 4)) (some (8, 10,
      4)) (.next ([6337500000000], [750000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([2983500000000], [397500000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([6022500000000],
      [1140000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([5940000000000], [1147500000000])
      (some (8, 10, 4)) (some (8, 10, 4)) (.next ([3756000000000], [772500000000]) (some (8, 10, 4))
      (some (8, 10, 4)) (.next ([3358500000000], [772500000000]) (some (8, 10, 4)) (some (8, 10, 4))
      (.next ([1522500000000], [397500000000]) (some (8, 10, 4)) (some (10, 10, 4)) (.next
      ([5625000000000], [1537500000000]) (some (10, 10, 4)) (some (10, 10, 4)) (.next
      ([5190000000000], [1522500000000]) (some (10, 10, 4)) (some (10, 10, 4))
      fan21Owner0Part1)))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded21_1 : ExcludedOn (model21.B 1 ++ [step21.q]) 9000000000000 (model21.caps 1)
    (model21.ord 1) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded21_2 : ExcludedOn (model21.B 2 ++ [step21.q]) 9000000000000 (model21.caps 2)
    (model21.ord 2) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded21_3 : ExcludedOn (model21.B 3 ++ [step21.q]) 9000000000000 (model21.caps 3)
    (model21.ord 3) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6051000000000, 9000000000000], [2574000000000,
      -9000000000000]) (some (2, 4, 1)) (some (3, 4, 1)) (.next ([4275000000000, -9000000000000],
      [2295000000000, 9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2295000000000,
      9000000000000], [2295000000000, 9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next
      ([1701000000000], [2055000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([3756000000000],
      [4869000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2295000000000, 9000000000000],
      [4275000000000, -9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([1461000000000,
      -9000000000000], [4869000000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next ([0],
      [2295000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-2574000000000,
      9000000000000], [8625000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2295000000000,
      -9000000000000], [6570000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2295000000000,
      -9000000000000], [4590000000000, 18000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-2055000000000], [3756000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-4869000000000], [8625000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4275000000000,
      9000000000000], [6570000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4869000000000],
      [6330000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2))
      (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded21_5 : ExcludedOn (model21.B 5 ++ [step21.q]) 9000000000000 (model21.caps 5)
    (model21.ord 5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded21_6 : ExcludedOn (model21.B 6 ++ [step21.q]) 9000000000000 (model21.caps 6)
    (model21.ord 6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded21_7 : ExcludedOn (model21.B 7 ++ [step21.q]) 9000000000000 (model21.caps 7)
    (model21.ord 7) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded21_8 : ExcludedOn (model21.B 8 ++ [step21.q]) 9000000000000 (model21.caps 8)
    (model21.ord 8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded21_9 : ExcludedOn (model21.B 9 ++ [step21.q]) 9000000000000 (model21.caps 9)
    (model21.ord 9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked21 : StepValid model21 9000000000000 step21 0 1 200 := by
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
    · exact (hj rfl).elim
    · exact excluded21_5
    · exact excluded21_6
    · exact excluded21_7
    · exact excluded21_8
    · exact excluded21_9
theorem next21 : model21.insert step21 = model22 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded22_0 : ExcludedOn (model22.B 0 ++ [step22.q]) 9000000000000 (model22.caps 0)
    (model22.ord 0) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded22_1 : ExcludedOn (model22.B 1 ++ [step22.q]) 9000000000000 (model22.caps 1)
    (model22.ord 1) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded22_2 : ExcludedOn (model22.B 2 ++ [step22.q]) 9000000000000 (model22.caps 2)
    (model22.ord 2) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded22_3 : ExcludedOn (model22.B 3 ++ [step22.q]) 9000000000000 (model22.caps 3)
    (model22.ord 3) 0 1 200 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded22_4 : ExcludedOn (model22.B 4 ++ [step22.q]) 9000000000000 (model22.caps 4)
    (model22.ord 4) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4869000000000], [375000000000]) (some (8, 0, 3))
      (some (8, 1, 3)) (.next ([5557500000000], [705000000000]) (some (8, 1, 3)) (some (8, 1, 3))
      (.next ([5295000000000], [1080000000000]) (some (8, 1, 3)) (some (8, 1, 3)) (.next
      ([1596000000000], [654000000000]) (some (8, 1, 3)) (some (8, 1, 3)) (.next ([4131000000000],
      [1875000000000]) (some (8, 1, 3)) (some (8, 1, 3)) (.next ([3375000000000], [2182500000000])
      (some (8, 1, 3)) (some (8, 1, 3)) (.next ([3000000000000], [2295000000000]) (some (8, 1, 3))
      (some (8, 1, 3)) (.next ([4680000000000], [4410000000000]) (some (8, 1, 3)) (some (8, 1, 3))
      (.next ([762000000000], [738000000000]) (some (8, 1, 3)) (some (8, 1, 3)) (.next
      ([2010000000000, -9000000000000], [2295000000000, 9000000000000]) (some (8, 1, 3)) (some (8,
      1, 4)) (.next ([1147500000000], [1410000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next
      ([3930000000000], [5244000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([307500000000],
      [448500000000]) (some (8, 1, 4)) (some (8, 1, 4)) fan22Owner4Part1)))))))))))))) (den :=
      9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded22_5 : ExcludedOn (model22.B 5 ++ [step22.q]) 9000000000000 (model22.caps 5)
    (model22.ord 5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded22_6 : ExcludedOn (model22.B 6 ++ [step22.q]) 9000000000000 (model22.caps 6)
    (model22.ord 6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded22_7 : ExcludedOn (model22.B 7 ++ [step22.q]) 9000000000000 (model22.caps 7)
    (model22.ord 7) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded22_9 : ExcludedOn (model22.B 9 ++ [step22.q]) 9000000000000 (model22.caps 9)
    (model22.ord 9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked22 : StepValid model22 9000000000000 step22 0 1 200 := by
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
    · exact excluded22_4
    · exact excluded22_5
    · exact excluded22_6
    · exact excluded22_7
    · exact (hj rfl).elim
    · exact excluded22_9
theorem next22 : model22.insert step22 = model23 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded23_0 : ExcludedOn (model23.B 0 ++ [step23.q]) 9000000000000 (model23.caps 0)
    (model23.ord 0) 0 1 200 := by
  apply ExclusionHint.sound (.pair 3 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded23_1 : ExcludedOn (model23.B 1 ++ [step23.q]) 9000000000000 (model23.caps 1)
    (model23.ord 1) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded23_2 : ExcludedOn (model23.B 2 ++ [step23.q]) 9000000000000 (model23.caps 2)
    (model23.ord 2) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded23_4 : ExcludedOn (model23.B 4 ++ [step23.q]) 9000000000000 (model23.caps 4)
    (model23.ord 4) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1836000000000], [45000000000]) (some (8, 0, 3))
      (some (8, 1, 3)) (.next ([4869000000000], [375000000000]) (some (8, 1, 3)) (some (8, 1, 3))
      (.next ([5557500000000], [705000000000]) (some (8, 1, 3)) (some (8, 1, 3)) (.next
      ([1948500000000], [307500000000]) (some (8, 1, 3)) (some (8, 1, 3)) (.next ([5295000000000],
      [1080000000000]) (some (8, 1, 3)) (some (8, 1, 3)) (.next ([2256000000000], [756000000000])
      (some (8, 1, 3)) (some (8, 1, 3)) (.next ([1596000000000], [654000000000]) (some (8, 1, 3))
      (some (8, 1, 3)) (.next ([4131000000000], [1875000000000]) (some (8, 1, 3)) (some (8, 1, 3))
      (.next ([5250000000000], [2961000000000]) (some (8, 1, 3)) (some (8, 1, 3)) (.next
      ([3375000000000], [2182500000000]) (some (8, 1, 3)) (some (8, 1, 3)) (.next ([3000000000000],
      [2295000000000]) (some (8, 1, 3)) (some (8, 1, 3)) (.next ([762000000000], [738000000000])
      (some (8, 1, 3)) (some (8, 1, 3)) (.next ([1147500000000], [1410000000000]) (some (8, 1, 3))
      (some (8, 1, 4)) (.next ([307500000000], [448500000000]) (some (8, 1, 4)) (some (8, 1, 4))
      (.next ([1920000000000, 9000000000000], [2949000000000, -9000000000000]) (some (8, 1, 4))
      (some (8, 1, 4)) (.next ([1119000000000], [1836000000000, -9000000000000]) (some (8, 1, 4))
      (some (8, 1, 4)) (.next ([420000000000], [711000000000]) (some (7, 1, 4)) (some (7, 1, 4))
      fan23Owner4Part1)))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded23_5 : ExcludedOn (model23.B 5 ++ [step23.q]) 9000000000000 (model23.caps 5)
    (model23.ord 5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded23_6 : ExcludedOn (model23.B 6 ++ [step23.q]) 9000000000000 (model23.caps 6)
    (model23.ord 6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded23_7 : ExcludedOn (model23.B 7 ++ [step23.q]) 9000000000000 (model23.caps 7)
    (model23.ord 7) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded23_8 : ExcludedOn (model23.B 8 ++ [step23.q]) 9000000000000 (model23.caps 8)
    (model23.ord 8) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4869000000000], [6000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([4869000000000], [5250000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([549000000000], [4695000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([174000000000], [5250000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [4695000000000]) (some (0, 1, 3)) (some (0, 3, 3)) (.next ([-6000000000], [4875000000000])
      (some (0, 3, 3)) (some (0, 3, 3)) (.next ([-5250000000000], [10119000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-4695000000000], [5244000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-5250000000000], [5424000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded23_9 : ExcludedOn (model23.B 9 ++ [step23.q]) 9000000000000 (model23.caps 9)
    (model23.ord 9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked23 : StepValid model23 9000000000000 step23 0 1 200 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded23_0
    · exact excluded23_1
    · exact excluded23_2
    · exact (hj rfl).elim
    · exact excluded23_4
    · exact excluded23_5
    · exact excluded23_6
    · exact excluded23_7
    · exact excluded23_8
    · exact excluded23_9
theorem next23 : model23.insert step23 = model24 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext255000260000
end ConwaySoifer.Simplified.Certificates
