/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint330000340000
import Mathlib.Tactic.FinCases

/-!
# Sint 330000 340000 1

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
namespace Sint330000340000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan12Owner0Part0 : FanWitness := (.next ([-1485000000000], [2970000000000]) (some (9, 4, 7))
    (some (9, 5, 7)) (.next ([-375000000000], [735000000000]) (some (9, 5, 7)) (some (9, 5, 7))
    (.next ([-96000000000], [165000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next
    ([-3861000000000], [6096000000000]) (some (9, 5, 7)) (some (9, 5, 8)) (.next ([-4125000000000],
    [6081000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-4236000000000], [6096000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-3750000000000], [5346000000000]) (some (9, 5, 8))
    (some (9, 5, 8)) (.next ([-4596000000000], [6471000000000]) (some (9, 5, 8)) (some (9, 5, 8))
    (.next ([-1860000000000], [2610000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-4305000000000], [6000000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-3568200000000,
    3960000000000], [4692600000000, -1980000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-4971000000000], [6471000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5249400000000,
    -1980000000000], [6652800000000, 3960000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-5040000000000], [6375000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-1485000000000],
    [1860000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5610000000000], [6831000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5624400000000, -1980000000000], [6652800000000,
    3960000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5693400000000, -1980000000000],
    [6556800000000, 3960000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5721000000000],
    [6471000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-3750000000000], [4221000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-6096000000000], [6471000000000]) (some (9, 5, 8))
    (some (9, 5, 8)) (.next ([-2041800000000, -3960000000000], [2138400000000, 1980000000000]) (some
    (9, 5, 8)) (some (9, 5, 8)) (.next ([-6165000000000], [6375000000000]) (some (9, 5, 8)) (some
    (9, 5, 8)) (.next ([-6081000000000], [6096000000000]) (some (9, 5, 8)) (some (9, 5, 8))
    (.terminal (some (9, 5, 8)) (some (9, 5, 8)) (some (9, 5, 8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan12Owner0Part1 : FanWitness := (.next ([1221000000000], [5610000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) (.next ([1028400000000, 1980000000000], [5624400000000, 1980000000000]) (some
    (9, 4, 6)) (some (9, 4, 6)) (.next ([863400000000, 1980000000000], [5693400000000,
    1980000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([750000000000], [5721000000000]) (some
    (9, 4, 6)) (some (9, 4, 6)) (.next ([471000000000], [3750000000000]) (some (9, 4, 6)) (some (9,
    4, 6)) (.next ([375000000000], [6096000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([96600000000, -1980000000000], [2041800000000, 3960000000000]) (some (9, 4, 6)) (some (9, 4,
    6)) (.next ([210000000000], [6165000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([15000000000], [6081000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([0], [2220000000000])
    (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-360000000000], [6456000000000]) (some (9, 4, 6))
    (some (9, 4, 7)) (.next ([-264000000000], [4125000000000]) (some (9, 4, 7)) (some (9, 4, 7))
    (.next ([-525000000000], [6525000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next
    ([-735000000000], [5346000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-96000000000],
    [540000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-1110000000000], [5721000000000])
    (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-375000000000], [1860000000000]) (some (9, 4, 7))
    (some (9, 4, 7)) (.next ([-1275000000000], [5790000000000]) (some (9, 4, 7)) (some (9, 4, 7))
    (.next ([-181800000000, -3960000000000], [653400000000, 1980000000000]) (some (9, 4, 7)) (some
    (9, 4, 7)) (.next ([-4125000000000], [10221000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next
    ([-4500000000000], [10221000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-4569000000000],
    [10125000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-360000000000], [735000000000])
    (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-735000000000], [1485000000000]) (some (9, 4, 7))
    (some (9, 4, 7)) fan12Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan12Owner0Part2 : FanWitness := (.next ([4611000000000], [1110000000000]) (some (8, 9, 6))
    (some (8, 9, 6)) (.next ([1485000000000], [375000000000]) (some (8, 9, 6)) (some (8, 9, 6))
    (.next ([4515000000000], [1275000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
    ([471600000000, -1980000000000], [181800000000, 3960000000000]) (some (8, 9, 6)) (some (8, 9,
    6)) (.next ([6096000000000], [4125000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
    ([5721000000000], [4500000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([5556000000000],
    [4569000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([375000000000], [360000000000]) (some
    (8, 9, 6)) (some (9, 9, 6)) (.next ([750000000000], [735000000000]) (some (9, 9, 6)) (some (9,
    9, 6)) (.next ([1485000000000], [1485000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next
    ([360000000000], [375000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next ([69000000000],
    [96000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next ([2235000000000], [3861000000000]) (some
    (9, 9, 6)) (some (9, 9, 6)) (.next ([1956000000000], [4125000000000]) (some (9, 9, 6)) (some (9,
    9, 6)) (.next ([1860000000000], [4236000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([1596000000000], [3750000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([1875000000000],
    [4596000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([750000000000], [1860000000000])
    (some (9, 4, 6)) (some (9, 4, 6)) (.next ([1695000000000], [4305000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) (.next ([1124400000000, 1980000000000], [3568200000000, -3960000000000]) (some
    (9, 4, 6)) (some (9, 4, 6)) (.next ([1500000000000], [4971000000000]) (some (9, 4, 6)) (some (9,
    4, 6)) (.next ([1403400000000, 1980000000000], [5249400000000, 1980000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) (.next ([1335000000000], [5040000000000]) (some (9, 4, 6)) (some (9, 4, 6))
    (.next ([375000000000], [1485000000000]) (some (9, 4, 6)) (some (9, 4, 6))
    fan12Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan13Owner0Part0 : FanWitness := (.next ([-735000000000], [1485000000000]) (some (9, 4, 7))
    (some (9, 4, 7)) (.next ([-1485000000000], [2970000000000]) (some (9, 4, 7)) (some (9, 5, 7))
    (.next ([-375000000000], [735000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next
    ([-96000000000], [165000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next ([-3861000000000],
    [6096000000000]) (some (9, 5, 7)) (some (9, 5, 8)) (.next ([-4236000000000], [6096000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-4596000000000], [6471000000000]) (some (9, 5, 8))
    (some (9, 5, 8)) (.next ([-1860000000000], [2610000000000]) (some (9, 5, 8)) (some (9, 5, 8))
    (.next ([-4125000000000], [5775000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-4305000000000], [6000000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-3750000000000],
    [5040000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-4971000000000], [6471000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5249400000000, -1980000000000], [6652800000000,
    3960000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5040000000000], [6375000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-1485000000000], [1860000000000]) (some (9, 5, 8))
    (some (9, 5, 8)) (.next ([-3568200000000, 3960000000000], [4386600000000, -1980000000000]) (some
    (9, 5, 8)) (some (9, 5, 8)) (.next ([-5624400000000, -1980000000000], [6652800000000,
    3960000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5610000000000], [6525000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5693400000000, -1980000000000], [6556800000000,
    3960000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5721000000000], [6471000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-6096000000000], [6471000000000]) (some (9, 5, 8))
    (some (9, 5, 8)) (.next ([-3750000000000], [3915000000000]) (some (9, 5, 8)) (some (9, 5, 8))
    (.next ([-6165000000000], [6375000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-6081000000000], [6096000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.terminal (some (9, 5,
    8)) (some (9, 5, 8)) (some (9, 5, 8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan13Owner0Part1 : FanWitness := (.next ([818400000000, 1980000000000], [3568200000000,
    -3960000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([1028400000000, 1980000000000],
    [5624400000000, 1980000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([915000000000],
    [5610000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([863400000000, 1980000000000],
    [5693400000000, 1980000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([750000000000],
    [5721000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([375000000000], [6096000000000])
    (some (9, 4, 6)) (some (9, 4, 6)) (.next ([165000000000], [3750000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) (.next ([210000000000], [6165000000000]) (some (9, 4, 6)) (some (9, 4, 6))
    (.next ([15000000000], [6081000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([0],
    [2220000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-360000000000], [6456000000000])
    (some (9, 4, 6)) (some (9, 4, 7)) (.next ([-525000000000], [6525000000000]) (some (9, 4, 7))
    (some (9, 4, 7)) (.next ([-735000000000], [5346000000000]) (some (9, 4, 7)) (some (9, 4, 7))
    (.next ([-570000000000], [4125000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next
    ([-96000000000], [540000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-1110000000000],
    [5721000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-375000000000], [1860000000000])
    (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-1275000000000], [5790000000000]) (some (9, 4, 7))
    (some (9, 4, 7)) (.next ([-181800000000, -3960000000000], [653400000000, 1980000000000]) (some
    (9, 4, 7)) (some (9, 4, 7)) (.next ([-556800000000, -3960000000000], [1388400000000,
    1980000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-4431000000000], [10221000000000])
    (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-4806000000000], [10221000000000]) (some (9, 4, 7))
    (some (9, 4, 7)) (.next ([-4875000000000], [10125000000000]) (some (9, 4, 7)) (some (9, 4, 7))
    (.next ([-360000000000], [735000000000]) (some (9, 4, 7)) (some (9, 4, 7))
    fan13Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan13Owner0Part2 : FanWitness := (.next ([4611000000000], [1110000000000]) (some (8, 9, 6))
    (some (8, 9, 6)) (.next ([1485000000000], [375000000000]) (some (8, 9, 6)) (some (8, 9, 6))
    (.next ([4515000000000], [1275000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
    ([471600000000, -1980000000000], [181800000000, 3960000000000]) (some (8, 9, 6)) (some (8, 9,
    6)) (.next ([831600000000, -1980000000000], [556800000000, 3960000000000]) (some (8, 9, 6))
    (some (8, 9, 6)) (.next ([5790000000000], [4431000000000]) (some (8, 9, 6)) (some (8, 9, 6))
    (.next ([5415000000000], [4806000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
    ([5250000000000], [4875000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([375000000000],
    [360000000000]) (some (8, 9, 6)) (some (9, 9, 6)) (.next ([750000000000], [735000000000]) (some
    (9, 9, 6)) (some (9, 9, 6)) (.next ([1485000000000], [1485000000000]) (some (9, 9, 6)) (some (9,
    9, 6)) (.next ([360000000000], [375000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next
    ([69000000000], [96000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next ([2235000000000],
    [3861000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next ([1860000000000], [4236000000000])
    (some (9, 9, 6)) (some (9, 9, 6)) (.next ([1875000000000], [4596000000000]) (some (9, 9, 6))
    (some (9, 9, 6)) (.next ([750000000000], [1860000000000]) (some (9, 9, 6)) (some (9, 9, 6))
    (.next ([1650000000000], [4125000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next
    ([1695000000000], [4305000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([1290000000000],
    [3750000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([1500000000000], [4971000000000])
    (some (9, 4, 6)) (some (9, 4, 6)) (.next ([1403400000000, 1980000000000], [5249400000000,
    1980000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([1335000000000], [5040000000000])
    (some (9, 4, 6)) (some (9, 4, 6)) (.next ([375000000000], [1485000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) fan13Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner0Part0 : FanWitness := (.next ([-4455000000000], [9330000000000]) (some (0, 4, 9))
    (some (0, 4, 9)) (.next ([-360000000000], [735000000000]) (some (0, 4, 9)) (some (0, 4, 9))
    (.next ([-735000000000], [1485000000000]) (some (0, 4, 9)) (some (1, 4, 9)) (.next
    ([-1485000000000], [2970000000000]) (some (1, 4, 9)) (some (1, 5, 9)) (.next ([-375000000000],
    [735000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-5190000000000], [9690000000000])
    (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-96000000000], [165000000000]) (some (1, 5, 9)) (some
    (1, 5, 9)) (.next ([-3861000000000], [6096000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next
    ([-5940000000000], [8955000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-4236000000000],
    [6096000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-4596000000000], [6471000000000])
    (some (1, 5, 9)) (some (2, 5, 9)) (.next ([-1860000000000], [2610000000000]) (some (2, 5, 9))
    (some (2, 5, 9)) (.next ([-4305000000000], [6000000000000]) (some (2, 5, 9)) (some (2, 5, 9))
    (.next ([-4971000000000], [6471000000000]) (some (2, 5, 9)) (some (2, 5, 9)) (.next
    ([-5249400000000, -1980000000000], [6652800000000, 3960000000000]) (some (2, 5, 9)) (some (2, 5,
    9)) (.next ([-5040000000000], [6375000000000]) (some (2, 5, 9)) (some (2, 5, 9)) (.next
    ([-1485000000000], [1860000000000]) (some (2, 5, 9)) (some (2, 5, 9)) (.next ([-5624400000000,
    -1980000000000], [6652800000000, 3960000000000]) (some (2, 5, 9)) (some (2, 5, 9)) (.next
    ([-5693400000000, -1980000000000], [6556800000000, 3960000000000]) (some (2, 5, 9)) (some (2, 5,
    9)) (.next ([-5721000000000], [6471000000000]) (some (2, 5, 9)) (some (2, 5, 9)) (.next
    ([-6096000000000], [6471000000000]) (some (2, 5, 9)) (some (2, 5, 9)) (.next ([-2041800000000,
    -3960000000000], [2138400000000, 1980000000000]) (some (2, 5, 9)) (some (2, 5, 9)) (.next
    ([-6165000000000], [6375000000000]) (some (2, 5, 9)) (some (2, 5, 9)) (.next ([-6081000000000],
    [6096000000000]) (some (2, 5, 9)) (some (2, 5, 9)) (.terminal (some (2, 5, 9)) (some (2, 5, 9))
    (some (2, 5, 9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner0Part1 : FanWitness := (.next ([1500000000000], [4971000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) (.next ([1403400000000, 1980000000000], [5249400000000, 1980000000000]) (some
    (9, 4, 6)) (some (9, 4, 6)) (.next ([1335000000000], [5040000000000]) (some (9, 4, 6)) (some (9,
    4, 6)) (.next ([375000000000], [1485000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([1028400000000, 1980000000000], [5624400000000, 1980000000000]) (some (9, 4, 6)) (some (9, 4,
    6)) (.next ([863400000000, 1980000000000], [5693400000000, 1980000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) (.next ([750000000000], [5721000000000]) (some (9, 4, 6)) (some (9, 4, 6))
    (.next ([375000000000], [6096000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([96600000000,
    -1980000000000], [2041800000000, 3960000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([210000000000], [6165000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([15000000000],
    [6081000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([0], [2220000000000]) (some (9, 4,
    6)) (some (9, 4, 6)) (.next ([-360000000000], [6456000000000]) (some (9, 4, 6)) (some (9, 4, 7))
    (.next ([-525000000000], [6525000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next
    ([-735000000000], [5346000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-96000000000],
    [540000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-1110000000000], [5721000000000])
    (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-375000000000], [1860000000000]) (some (9, 4, 7))
    (some (9, 4, 7)) (.next ([-1275000000000], [5790000000000]) (some (9, 4, 7)) (some (9, 4, 7))
    (.next ([-181800000000, -3960000000000], [653400000000, 1980000000000]) (some (9, 4, 7)) (some
    (9, 4, 7)) (.next ([-1596000000000], [4830000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next
    ([-2970000000000], [7470000000000]) (some (9, 4, 7)) (some (9, 4, 9)) (.next ([-3330000000000],
    [8205000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-3801600000000, 1980000000000],
    [8858400000000, 1980000000000]) (some (0, 4, 9)) (some (0, 4, 9))
    fan14Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner0Part2 : FanWitness := (.next ([6000000000000], [525000000000]) (some (9, 2, 5)) (some
    (9, 2, 5)) (.next ([4611000000000], [735000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next
    ([444000000000], [96000000000]) (some (9, 2, 5)) (some (9, 2, 6)) (.next ([4611000000000],
    [1110000000000]) (some (9, 2, 6)) (some (9, 2, 6)) (.next ([1485000000000], [375000000000])
    (some (9, 2, 6)) (some (9, 2, 6)) (.next ([4515000000000], [1275000000000]) (some (9, 2, 6))
    (some (9, 2, 6)) (.next ([471600000000, -1980000000000], [181800000000, 3960000000000]) (some
    (9, 2, 6)) (some (9, 2, 6)) (.next ([3234000000000], [1596000000000]) (some (9, 2, 6)) (some (9,
    3, 6)) (.next ([4500000000000], [2970000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next
    ([4875000000000], [3330000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([5056800000000,
    3960000000000], [3801600000000, -1980000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next
    ([4875000000000], [4455000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([375000000000],
    [360000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([750000000000], [735000000000]) (some
    (9, 3, 6)) (some (9, 3, 6)) (.next ([1485000000000], [1485000000000]) (some (9, 3, 6)) (some (9,
    3, 6)) (.next ([360000000000], [375000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next
    ([4500000000000], [5190000000000]) (some (9, 3, 6)) (some (9, 4, 6)) (.next ([69000000000],
    [96000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([2235000000000], [3861000000000]) (some
    (9, 4, 6)) (some (9, 4, 6)) (.next ([3015000000000], [5940000000000]) (some (9, 4, 6)) (some (9,
    4, 6)) (.next ([1860000000000], [4236000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([1875000000000], [4596000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([750000000000],
    [1860000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([1695000000000], [4305000000000])
    (some (9, 4, 6)) (some (9, 4, 6)) fan14Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner0Part0 : FanWitness := (.next ([-1485000000000], [2970000000000]) (some (9, 9, 7))
    (some (9, 9, 7)) (.next ([-375000000000], [735000000000]) (some (9, 9, 7)) (some (9, 9, 7))
    (.next ([-2010000000000], [3495000000000]) (some (9, 9, 7)) (some (9, 9, 7)) (.next
    ([-96000000000], [165000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next ([-3861000000000],
    [6096000000000]) (some (9, 5, 7)) (some (9, 5, 8)) (.next ([-1275000000000], [2010000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-4236000000000], [6096000000000]) (some (9, 5, 8))
    (some (9, 5, 8)) (.next ([-4596000000000], [6471000000000]) (some (9, 5, 8)) (some (9, 5, 8))
    (.next ([-1860000000000], [2610000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-4305000000000], [6000000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-4971000000000],
    [6471000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5249400000000, -1980000000000],
    [6652800000000, 3960000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5040000000000],
    [6375000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-1485000000000], [1860000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5624400000000, -1980000000000], [6652800000000,
    3960000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5693400000000, -1980000000000],
    [6556800000000, 3960000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5721000000000],
    [6471000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-7356000000000], [8106000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-6096000000000], [6471000000000]) (some (9, 5, 8))
    (some (9, 5, 8)) (.next ([-7731000000000], [8106000000000]) (some (9, 5, 8)) (some (9, 5, 8))
    (.next ([-2041800000000, -3960000000000], [2138400000000, 1980000000000]) (some (9, 5, 8)) (some
    (9, 5, 8)) (.next ([-6165000000000], [6375000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-7800000000000], [8010000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-6081000000000],
    [6096000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.terminal (some (9, 5, 8)) (some (9, 5, 8))
    (some (9, 5, 8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner0Part1 : FanWitness := (.next ([375000000000], [1485000000000]) (some (0, 9, 6)) (some
    (0, 9, 6)) (.next ([1028400000000, 1980000000000], [5624400000000, 1980000000000]) (some (0, 9,
    6)) (some (0, 9, 6)) (.next ([863400000000, 1980000000000], [5693400000000, 1980000000000])
    (some (0, 9, 6)) (some (0, 9, 6)) (.next ([750000000000], [5721000000000]) (some (0, 9, 6))
    (some (0, 9, 6)) (.next ([750000000000], [7356000000000]) (some (0, 9, 6)) (some (0, 9, 6))
    (.next ([375000000000], [6096000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next
    ([375000000000], [7731000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([96600000000,
    -1980000000000], [2041800000000, 3960000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next
    ([210000000000], [6165000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([210000000000],
    [7800000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([15000000000], [6081000000000]) (some
    (0, 9, 6)) (some (0, 9, 6)) (.next ([0], [2220000000000]) (some (0, 9, 6)) (some (0, 9, 6))
    (.next ([-360000000000], [6456000000000]) (some (0, 9, 6)) (some (0, 9, 7)) (.next
    ([-525000000000], [6525000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-735000000000],
    [5346000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-96000000000], [540000000000]) (some
    (0, 9, 7)) (some (0, 9, 7)) (.next ([-1110000000000], [5721000000000]) (some (0, 9, 7)) (some
    (0, 9, 7)) (.next ([-375000000000], [1860000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next
    ([-1275000000000], [5790000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-181800000000,
    -3960000000000], [653400000000, 1980000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next
    ([-1125000000000], [2760000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-1485000000000],
    [3495000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-360000000000], [735000000000])
    (some (0, 9, 7)) (some (9, 9, 7)) (.next ([-735000000000], [1485000000000]) (some (9, 9, 7))
    (some (9, 9, 7)) fan15Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner0Part2 : FanWitness := (.next ([6000000000000], [525000000000]) (some (8, 9, 5)) (some
    (8, 9, 5)) (.next ([4611000000000], [735000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next
    ([444000000000], [96000000000]) (some (8, 9, 5)) (some (8, 9, 6)) (.next ([4611000000000],
    [1110000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([1485000000000], [375000000000])
    (some (8, 9, 6)) (some (8, 9, 6)) (.next ([4515000000000], [1275000000000]) (some (8, 9, 6))
    (some (8, 9, 6)) (.next ([471600000000, -1980000000000], [181800000000, 3960000000000]) (some
    (8, 9, 6)) (some (8, 9, 6)) (.next ([1635000000000], [1125000000000]) (some (8, 9, 6)) (some (8,
    9, 6)) (.next ([2010000000000], [1485000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
    ([375000000000], [360000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([750000000000],
    [735000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([1485000000000], [1485000000000])
    (some (8, 9, 6)) (some (8, 9, 6)) (.next ([360000000000], [375000000000]) (some (8, 9, 6)) (some
    (8, 9, 6)) (.next ([1485000000000], [2010000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
    ([69000000000], [96000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([2235000000000],
    [3861000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([735000000000], [1275000000000])
    (some (8, 9, 6)) (some (8, 9, 6)) (.next ([1860000000000], [4236000000000]) (some (8, 9, 6))
    (some (8, 9, 6)) (.next ([1875000000000], [4596000000000]) (some (8, 9, 6)) (some (8, 9, 6))
    (.next ([750000000000], [1860000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
    ([1695000000000], [4305000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([1500000000000],
    [4971000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([1403400000000, 1980000000000],
    [5249400000000, 1980000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([1335000000000],
    [5040000000000]) (some (0, 9, 6)) (some (0, 9, 6)) fan15Owner0Part1))))))))))))))))))))))))

theorem excluded8_1 : ExcludedOn (model8.B 1 ++ [step8.q]) 9000000000000 (model8.caps 1) (model8.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_2 : ExcludedOn (model8.B 2 ++ [step8.q]) 9000000000000 (model8.caps 2) (model8.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_3 : ExcludedOn (model8.B 3 ++ [step8.q]) 9000000000000 (model8.caps 3) (model8.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_4 : ExcludedOn (model8.B 4 ++ [step8.q]) 9000000000000 (model8.caps 4) (model8.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_5 : ExcludedOn (model8.B 5 ++ [step8.q]) 9000000000000 (model8.caps 5) (model8.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5280000000000, -9000000000000], [2235000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([2970000000000, 9000000000000],
      [2970000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([3705000000000,
      9000000000000], [4545000000000, -9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next
      ([735000000000], [7515000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0],
      [2970000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2235000000000,
      -9000000000000], [7515000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-2970000000000,
      -9000000000000], [5940000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-4545000000000, 9000000000000], [8250000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-7515000000000], [8250000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_6 : ExcludedOn (model8.B 6 ++ [step8.q]) 9000000000000 (model8.caps 6) (model8.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7515000000000], [750000000000]) (some (3, 0, 1))
      (some (3, 0, 2)) (.next ([4545000000000, -9000000000000], [3720000000000, 9000000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2970000000000, 9000000000000], [2970000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2220000000000, 9000000000000],
      [5295000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [2970000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-750000000000],
      [8265000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-3720000000000, -9000000000000],
      [8265000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2970000000000, -9000000000000],
      [5940000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-5295000000000,
      9000000000000], [7515000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.terminal (some (0, 1, 3))
      (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_7 : ExcludedOn (model8.B 7 ++ [step8.q]) 9000000000000 (model8.caps 7) (model8.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_8 : ExcludedOn (model8.B 8 ++ [step8.q]) 9000000000000 (model8.caps 8) (model8.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_9 : ExcludedOn (model8.B 9 ++ [step8.q]) 9000000000000 (model8.caps 9) (model8.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked8 : StepValid model8 9000000000000 step8 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded8_1
    · exact excluded8_2
    · exact excluded8_3
    · exact excluded8_4
    · exact excluded8_5
    · exact excluded8_6
    · exact excluded8_7
    · exact excluded8_8
    · exact excluded8_9
theorem next8 : model8.insert step8 = model9 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded9_1 : ExcludedOn (model9.B 1 ++ [step9.q]) 9000000000000 (model9.caps 1) (model9.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7566000000000, 9000000000000], [684000000000,
      -9000000000000]) none none (.next ([4596000000000], [3654000000000]) none none (.next
      ([2970000000000, 9000000000000], [2970000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([1626000000000, -9000000000000], [3654000000000, 0]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([0, 0], [2970000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-684000000000, 9000000000000], [8250000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-3654000000000], [8250000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2970000000000,
      -9000000000000], [5940000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-3654000000000, 0], [5280000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.terminal (some (3, 1, 0)) none none))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_2 : ExcludedOn (model9.B 2 ++ [step9.q]) 9000000000000 (model9.caps 2) (model9.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3654000000000], [750000000000]) (some (0, 3, 1))
      (some (0, 3, 1)) (.next ([6030000000000, -9000000000000], [2970000000000, 9000000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1626000000000, -9000000000000], [3654000000000, 0])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([684000000000, -9000000000000], [3720000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [2970000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-750000000000], [4404000000000])
      (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-2970000000000, -9000000000000], [9000000000000,
      0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3654000000000, 0], [5280000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3720000000000, -9000000000000],
      [4404000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_3 : ExcludedOn (model9.B 3 ++ [step9.q]) 9000000000000 (model9.caps 3) (model9.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_4 : ExcludedOn (model9.B 4 ++ [step9.q]) 9000000000000 (model9.caps 4) (model9.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_5 : ExcludedOn (model9.B 5 ++ [step9.q]) 9000000000000 (model9.caps 5) (model9.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_6 : ExcludedOn (model9.B 6 ++ [step9.q]) 9000000000000 (model9.caps 6) (model9.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_7 : ExcludedOn (model9.B 7 ++ [step9.q]) 9000000000000 (model9.caps 7) (model9.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_8 : ExcludedOn (model9.B 8 ++ [step9.q]) 9000000000000 (model9.caps 8) (model9.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_9 : ExcludedOn (model9.B 9 ++ [step9.q]) 9000000000000 (model9.caps 9) (model9.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked9 : StepValid model9 9000000000000 step9 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded9_1
    · exact excluded9_2
    · exact excluded9_3
    · exact excluded9_4
    · exact excluded9_5
    · exact excluded9_6
    · exact excluded9_7
    · exact excluded9_8
    · exact excluded9_9
theorem next9 : model9.insert step9 = model10 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded10_1 : ExcludedOn (model10.B 1 ++ [step10.q]) 9000000000000 (model10.caps 1)
    (model10.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7515000000000], [750000000000]) (some (0, 3, 1))
      (some (0, 3, 2)) (.next ([4545000000000, -9000000000000], [3720000000000, 9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([2970000000000, 9000000000000], [2970000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([2220000000000, 9000000000000],
      [5295000000000, -9000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next ([0, 0],
      [2970000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-750000000000],
      [8265000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-3720000000000, -9000000000000],
      [8265000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2970000000000,
      -9000000000000], [5940000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-5295000000000, 9000000000000], [7515000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded10_2 : ExcludedOn (model10.B 2 ++ [step10.q]) 9000000000000 (model10.caps 2)
    (model10.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_3 : ExcludedOn (model10.B 3 ++ [step10.q]) 9000000000000 (model10.caps 3)
    (model10.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_4 : ExcludedOn (model10.B 4 ++ [step10.q]) 9000000000000 (model10.caps 4)
    (model10.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_5 : ExcludedOn (model10.B 5 ++ [step10.q]) 9000000000000 (model10.caps 5)
    (model10.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_6 : ExcludedOn (model10.B 6 ++ [step10.q]) 9000000000000 (model10.caps 6)
    (model10.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5280000000000, -9000000000000], [2235000000000,
      9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([2970000000000, 9000000000000],
      [2970000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([3705000000000,
      9000000000000], [4545000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([735000000000], [7515000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [2970000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-2235000000000,
      -9000000000000], [7515000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-2970000000000,
      -9000000000000], [5940000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next
      ([-4545000000000, 9000000000000], [8250000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next
      ([-7515000000000], [8250000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1,
      3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded10_7 : ExcludedOn (model10.B 7 ++ [step10.q]) 9000000000000 (model10.caps 7)
    (model10.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_8 : ExcludedOn (model10.B 8 ++ [step10.q]) 9000000000000 (model10.caps 8)
    (model10.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_9 : ExcludedOn (model10.B 9 ++ [step10.q]) 9000000000000 (model10.caps 9)
    (model10.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked10 : StepValid model10 9000000000000 step10 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded10_1
    · exact excluded10_2
    · exact excluded10_3
    · exact excluded10_4
    · exact excluded10_5
    · exact excluded10_6
    · exact excluded10_7
    · exact excluded10_8
    · exact excluded10_9
theorem next10 : model10.insert step10 = model11 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded11_0 : ExcludedOn (model11.B 0 ++ [step11.q]) 9000000000000 (model11.caps 0)
    (model11.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_1 : ExcludedOn (model11.B 1 ++ [step11.q]) 9000000000000 (model11.caps 1)
    (model11.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_2 : ExcludedOn (model11.B 2 ++ [step11.q]) 9000000000000 (model11.caps 2)
    (model11.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_3 : ExcludedOn (model11.B 3 ++ [step11.q]) 9000000000000 (model11.caps 3)
    (model11.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_4 : ExcludedOn (model11.B 4 ++ [step11.q]) 9000000000000 (model11.caps 4)
    (model11.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_5 : ExcludedOn (model11.B 5 ++ [step11.q]) 9000000000000 (model11.caps 5)
    (model11.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_6 : ExcludedOn (model11.B 6 ++ [step11.q]) 9000000000000 (model11.caps 6)
    (model11.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_7 : ExcludedOn (model11.B 7 ++ [step11.q]) 9000000000000 (model11.caps 7)
    (model11.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_9 : ExcludedOn (model11.B 9 ++ [step11.q]) 9000000000000 (model11.caps 9)
    (model11.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked11 : StepValid model11 9000000000000 step11 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded11_0
    · exact excluded11_1
    · exact excluded11_2
    · exact excluded11_3
    · exact excluded11_4
    · exact excluded11_5
    · exact excluded11_6
    · exact excluded11_7
    · exact (hj rfl).elim
    · exact excluded11_9
theorem next11 : model11.insert step11 = model12 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded12_0 : ExcludedOn (model12.B 0 ++ [step12.q]) 9000000000000 (model12.caps 0)
    (model12.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6096000000000], [360000000000]) (some (8, 9, 5))
      (some (8, 9, 5)) (.next ([3861000000000], [264000000000]) (some (8, 9, 5)) (some (8, 9, 5))
      (.next ([6000000000000], [525000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next
      ([4611000000000], [735000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([444000000000],
      [96000000000]) (some (8, 9, 5)) (some (8, 9, 6)) fan12Owner0Part2)))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded12_1 : ExcludedOn (model12.B 1 ++ [step12.q]) 9000000000000 (model12.caps 1)
    (model12.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_2 : ExcludedOn (model12.B 2 ++ [step12.q]) 9000000000000 (model12.caps 2)
    (model12.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_3 : ExcludedOn (model12.B 3 ++ [step12.q]) 9000000000000 (model12.caps 3)
    (model12.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_5 : ExcludedOn (model12.B 5 ++ [step12.q]) 9000000000000 (model12.caps 5)
    (model12.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000, 0], [2376000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([2970000000000, 9000000000000],
      [2970000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([4125000000000],
      [5346000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1155000000000, -9000000000000],
      [8316000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [2970000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-2376000000000,
      9000000000000], [6501000000000, -9000000000000]) (some (3, 1, 3)) (some (3, 2, 3)) (.next
      ([-2970000000000, -9000000000000], [5940000000000, 18000000000000]) (some (0, 2, 3)) (some (0,
      2, 3)) (.next ([-5346000000000], [9471000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-8316000000000, -9000000000000], [9471000000000]) (some (0, 2, 3)) (some (0, 2, 3))
      (.terminal (some (0, 2, 3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded12_6 : ExcludedOn (model12.B 6 ++ [step12.q]) 9000000000000 (model12.caps 6)
    (model12.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_7 : ExcludedOn (model12.B 7 ++ [step12.q]) 9000000000000 (model12.caps 7)
    (model12.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_8 : ExcludedOn (model12.B 8 ++ [step12.q]) 9000000000000 (model12.caps 8)
    (model12.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_9 : ExcludedOn (model12.B 9 ++ [step12.q]) 9000000000000 (model12.caps 9)
    (model12.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked12 : StepValid model12 9000000000000 step12 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded12_0
    · exact excluded12_1
    · exact excluded12_2
    · exact excluded12_3
    · exact (hj rfl).elim
    · exact excluded12_5
    · exact excluded12_6
    · exact excluded12_7
    · exact excluded12_8
    · exact excluded12_9
theorem next12 : model12.insert step12 = model13 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded13_0 : ExcludedOn (model13.B 0 ++ [step13.q]) 9000000000000 (model13.caps 0)
    (model13.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6096000000000], [360000000000]) (some (8, 9, 5))
      (some (8, 9, 5)) (.next ([6000000000000], [525000000000]) (some (8, 9, 5)) (some (8, 9, 5))
      (.next ([4611000000000], [735000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next
      ([3555000000000], [570000000000]) (some (8, 9, 5)) (some (8, 9, 6)) (.next ([444000000000],
      [96000000000]) (some (8, 9, 6)) (some (8, 9, 6)) fan13Owner0Part2)))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_1 : ExcludedOn (model13.B 1 ++ [step13.q]) 9000000000000 (model13.caps 1)
    (model13.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_2 : ExcludedOn (model13.B 2 ++ [step13.q]) 9000000000000 (model13.caps 2)
    (model13.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_3 : ExcludedOn (model13.B 3 ++ [step13.q]) 9000000000000 (model13.caps 3)
    (model13.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_5 : ExcludedOn (model13.B 5 ++ [step13.q]) 9000000000000 (model13.caps 5)
    (model13.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000, 0], [2070000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([2970000000000, 9000000000000],
      [2970000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([4125000000000],
      [5040000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1155000000000, -9000000000000],
      [8010000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [2970000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-2070000000000,
      9000000000000], [6195000000000, -9000000000000]) (some (3, 1, 3)) (some (3, 2, 3)) (.next
      ([-2970000000000, -9000000000000], [5940000000000, 18000000000000]) (some (0, 2, 3)) (some (0,
      2, 3)) (.next ([-5040000000000], [9165000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-8010000000000, -9000000000000], [9165000000000]) (some (0, 2, 3)) (some (0, 2, 3))
      (.terminal (some (0, 2, 3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_6 : ExcludedOn (model13.B 6 ++ [step13.q]) 9000000000000 (model13.caps 6)
    (model13.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_7 : ExcludedOn (model13.B 7 ++ [step13.q]) 9000000000000 (model13.caps 7)
    (model13.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_8 : ExcludedOn (model13.B 8 ++ [step13.q]) 9000000000000 (model13.caps 8)
    (model13.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_9 : ExcludedOn (model13.B 9 ++ [step13.q]) 9000000000000 (model13.caps 9)
    (model13.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked13 : StepValid model13 9000000000000 step13 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded13_0
    · exact excluded13_1
    · exact excluded13_2
    · exact excluded13_3
    · exact (hj rfl).elim
    · exact excluded13_5
    · exact excluded13_6
    · exact excluded13_7
    · exact excluded13_8
    · exact excluded13_9
theorem next13 : model13.insert step13 = model14 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded14_0 : ExcludedOn (model14.B 0 ++ [step14.q]) 9000000000000 (model14.caps 0)
    (model14.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6096000000000], [360000000000]) (some (9, 2, 5))
      (some (9, 2, 5)) fan14Owner0Part2)) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded14_1 : ExcludedOn (model14.B 1 ++ [step14.q]) 9000000000000 (model14.caps 1)
    (model14.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_2 : ExcludedOn (model14.B 2 ++ [step14.q]) 9000000000000 (model14.caps 2)
    (model14.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_4 : ExcludedOn (model14.B 4 ++ [step14.q]) 9000000000000 (model14.caps 4)
    (model14.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_5 : ExcludedOn (model14.B 5 ++ [step14.q]) 9000000000000 (model14.caps 5)
    (model14.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_6 : ExcludedOn (model14.B 6 ++ [step14.q]) 9000000000000 (model14.caps 6)
    (model14.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_7 : ExcludedOn (model14.B 7 ++ [step14.q]) 9000000000000 (model14.caps 7)
    (model14.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_8 : ExcludedOn (model14.B 8 ++ [step14.q]) 9000000000000 (model14.caps 8)
    (model14.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_9 : ExcludedOn (model14.B 9 ++ [step14.q]) 9000000000000 (model14.caps 9)
    (model14.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked14 : StepValid model14 9000000000000 step14 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded14_0
    · exact excluded14_1
    · exact excluded14_2
    · exact (hj rfl).elim
    · exact excluded14_4
    · exact excluded14_5
    · exact excluded14_6
    · exact excluded14_7
    · exact excluded14_8
    · exact excluded14_9
theorem next14 : model14.insert step14 = model15 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded15_0 : ExcludedOn (model15.B 0 ++ [step15.q]) 9000000000000 (model15.caps 0)
    (model15.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6096000000000], [360000000000]) (some (8, 9, 5))
      (some (8, 9, 5)) fan15Owner0Part2)) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded15_1 : ExcludedOn (model15.B 1 ++ [step15.q]) 9000000000000 (model15.caps 1)
    (model15.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_2 : ExcludedOn (model15.B 2 ++ [step15.q]) 9000000000000 (model15.caps 2)
    (model15.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_3 : ExcludedOn (model15.B 3 ++ [step15.q]) 9000000000000 (model15.caps 3)
    (model15.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_4 : ExcludedOn (model15.B 4 ++ [step15.q]) 9000000000000 (model15.caps 4)
    (model15.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3960000000000], [165000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) (.next ([3654000000000], [471000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([2805000000000, 9000000000000], [1155000000000, -9000000000000]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([2499000000000, 9000000000000], [1155000000000, -9000000000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([5730000000000, 9000000000000], [3270000000000,
      -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([3231000000000], [2115000000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2925000000000], [2115000000000]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([2970000000000, 9000000000000], [2970000000000, 9000000000000]) (some
      (4, 1, 5)) (some (4, 1, 5)) (.next ([2760000000000], [6240000000000]) (some (4, 1, 5)) (some
      (4, 1, 5)) (.next ([990000000000, -9000000000000], [3135000000000, 9000000000000]) (some (4,
      1, 5)) (some (4, 1, 5)) (.next ([684000000000, -9000000000000], [3441000000000,
      9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0, 0], [2970000000000,
      9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([-165000000000], [4125000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-471000000000], [4125000000000]) (some (0, 1, 5))
      (some (0, 5, 5)) (.next ([-1155000000000, 9000000000000], [3960000000000]) (some (0, 5, 5))
      (some (0, 5, 5)) (.next ([-1155000000000, 9000000000000], [3654000000000]) (some (0, 5, 5))
      (some (0, 5, 5)) (.next ([-3270000000000, 9000000000000], [9000000000000]) (some (0, 5, 5))
      (some (0, 5, 5)) (.next ([-2115000000000], [5346000000000]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([-2115000000000], [5040000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-2970000000000, -9000000000000], [5940000000000, 18000000000000]) (some (0, 5, 4)) (some (0,
      5, 4)) (.next ([-6240000000000], [9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-3135000000000, -9000000000000], [4125000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([-3441000000000, -9000000000000], [4125000000000, 0]) (some (0, 5, 4)) (some (0, 5,
      4)) (.terminal (some (0, 5, 4)) (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded15_6 : ExcludedOn (model15.B 6 ++ [step15.q]) 9000000000000 (model15.caps 6)
    (model15.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6240000000000], [2760000000000]) (some (3, 0,
      1)) (some (3, 0, 2)) (.next ([2970000000000, 9000000000000], [2970000000000, 9000000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([3270000000000, -9000000000000], [5730000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([210000000000, 9000000000000],
      [6030000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [2970000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-2760000000000],
      [9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-2970000000000, -9000000000000],
      [5940000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-5730000000000,
      -9000000000000], [9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-6030000000000,
      9000000000000], [6240000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.terminal (some (0, 1, 3))
      (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded15_7 : ExcludedOn (model15.B 7 ++ [step15.q]) 9000000000000 (model15.caps 7)
    (model15.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_8 : ExcludedOn (model15.B 8 ++ [step15.q]) 9000000000000 (model15.caps 8)
    (model15.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_9 : ExcludedOn (model15.B 9 ++ [step15.q]) 9000000000000 (model15.caps 9)
    (model15.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked15 : StepValid model15 9000000000000 step15 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded15_0
    · exact excluded15_1
    · exact excluded15_2
    · exact excluded15_3
    · exact excluded15_4
    · exact (hj rfl).elim
    · exact excluded15_6
    · exact excluded15_7
    · exact excluded15_8
    · exact excluded15_9
theorem next15 : model15.insert step15 = model16 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint330000340000
end ConwaySoifer.Simplified.Certificates
