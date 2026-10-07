/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint180000190000
import Mathlib.Tactic.FinCases

/-!
# Sint 180000 190000 5

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
namespace Sint180000190000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan40Owner5Part0 : FanWitness := (.next ([4836000000000], [24000000000]) (some (3, 1, 5)) (some
    (4, 1, 5)) (.next ([1110000000000], [15000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([4860000000000], [414000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([3765000000000],
    [375000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([2145000000000, -9000000000000],
    [375000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([5250000000000, 0], [1620000000000,
    9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([4890000000000], [3015000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([3240000000000, -9000000000000], [2034000000000,
    9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([4875000000000], [4140000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([1125000000000], [4140000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([720000000000], [4179000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([0], [5250000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-9000000000],
    [3735000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-24000000000], [4860000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-15000000000], [1125000000000]) (some (0, 2, 3))
    (some (0, 2, 3)) (.next ([-414000000000], [5274000000000]) (some (0, 2, 3)) (some (0, 2, 3))
    (.next ([-375000000000], [4140000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([-375000000000, 0], [2520000000000, -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([-1620000000000, -9000000000000], [6870000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 5,
    3)) (.next ([-3015000000000], [7905000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-2034000000000, -9000000000000], [5274000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-4140000000000], [9015000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4140000000000],
    [5265000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4179000000000], [4899000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5,
    3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan40Owner9Part0 : FanWitness := (.next ([2385000000000], [1905000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([2145000000000], [1770000000000]) (some (5, 1, 2)) (some (5, 1, 2))
    (.next ([2610000000000], [2655000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([2370000000000], [2520000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([4140000000000],
    [5235000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1620000000000], [4860000000000])
    (some (5, 1, 2)) (some (5, 1, 2)) (.next ([225000000000], [750000000000]) (some (5, 1, 2)) (some
    (5, 1, 2)) (.next ([1485000000000], [5235000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([750000000000], [4290000000000]) (some (5, 1, 2)) (some (5, 1, 5)) (.next ([30000000000],
    [4110000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([0], [5265000000000]) (some (0, 1,
    5)) (some (0, 1, 5)) (.next ([-375000000000], [2895000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-945000000000], [4335000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-135000000000], [375000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1905000000000],
    [4290000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1770000000000], [3915000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2655000000000], [5265000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-2520000000000], [4890000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-5235000000000], [9375000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-4860000000000], [6480000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-750000000000],
    [975000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5235000000000], [6720000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4290000000000], [5040000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-4110000000000], [4140000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.terminal (some (0, 1, 5)) (some (0, 1, 5)) (some (0, 1, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan44Owner3Part0 : FanWitness := (.next ([6255000000000], [810000000000]) (some (4, 1, 5)) (some
    (4, 1, 5)) (.next ([7020000000000], [1605000000000]) (some (4, 1, 5)) (some (4, 5, 5)) (.next
    ([6210000000000], [1620000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([5010000000000], [1485000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([5685000000000],
    [2055000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([5460000000000], [2370000000000])
    (some (4, 5, 3)) (some (4, 5, 3)) (.next ([1620000000000], [750000000000]) (some (4, 5, 3))
    (some (4, 5, 3)) (.next ([450000000000], [885000000000]) (some (4, 5, 3)) (some (4, 5, 3))
    (.next ([885000000000], [4875000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([810000000000], [7815000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0], [1620000000000,
    9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0, -9000000000000], [750000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-810000000000, -9000000000000], [7815000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-735000000000, -9000000000000], [6495000000000,
    9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-810000000000], [7065000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1605000000000], [8625000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-1620000000000, -9000000000000], [7830000000000, 9000000000000]) (some
    (0, 5, 3)) (some (0, 5, 3)) (.next ([-1485000000000], [6495000000000]) (some (0, 5, 3)) (some
    (0, 5, 3)) (.next ([-2055000000000], [7740000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-2370000000000], [7830000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-750000000000],
    [2370000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-885000000000], [1335000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4875000000000], [5760000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-7815000000000], [8625000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan44Owner3Part1 : FanWitness := (.next ([5760000000000], [735000000000, 9000000000000]) (some
    (4, 1, 5)) (some (4, 5, 5)) (.next ([7020000000000], [1605000000000]) (some (4, 5, 5)) (some (4,
    5, 5)) (.next ([6210000000000], [1620000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5,
    3)) (.next ([5010000000000], [1485000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([5685000000000], [2055000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([5460000000000],
    [2370000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([1620000000000], [750000000000])
    (some (4, 5, 3)) (some (4, 5, 3)) (.next ([450000000000], [885000000000]) (some (4, 5, 3)) (some
    (4, 5, 3)) (.next ([885000000000], [4875000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([810000000000], [7815000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0], [1620000000000,
    9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0, -9000000000000], [750000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-810000000000, -9000000000000], [7815000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-810000000000], [7065000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-735000000000, -9000000000000], [6495000000000, 9000000000000]) (some
    (0, 5, 3)) (some (0, 5, 3)) (.next ([-1605000000000], [8625000000000]) (some (0, 5, 3)) (some
    (0, 5, 3)) (.next ([-1620000000000, -9000000000000], [7830000000000, 9000000000000]) (some (0,
    5, 3)) (some (0, 5, 3)) (.next ([-1485000000000], [6495000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([-2055000000000], [7740000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-2370000000000], [7830000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-750000000000],
    [2370000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-885000000000], [1335000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4875000000000], [5760000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-7815000000000], [8625000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan44Owner3Part2 : FanWitness := (.next ([5760000000000], [735000000000, 9000000000000]) (some
    (4, 5, 5)) (some (4, 5, 5)) (.next ([7020000000000], [1605000000000]) (some (4, 5, 5)) (some (4,
    5, 5)) (.next ([6210000000000], [1620000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5,
    3)) (.next ([5010000000000], [1485000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([5685000000000], [2055000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([5460000000000],
    [2370000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([1620000000000], [750000000000])
    (some (4, 5, 3)) (some (4, 5, 3)) (.next ([450000000000], [885000000000]) (some (4, 5, 3)) (some
    (4, 5, 3)) (.next ([885000000000], [4875000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([810000000000], [7815000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0], [1620000000000,
    9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([-810000000000], [7065000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-810000000000, -9000000000000], [7815000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0, -9000000000000], [750000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-735000000000, -9000000000000], [6495000000000, 9000000000000]) (some
    (0, 5, 3)) (some (0, 5, 3)) (.next ([-1605000000000], [8625000000000]) (some (0, 5, 3)) (some
    (0, 5, 3)) (.next ([-1620000000000, -9000000000000], [7830000000000, 9000000000000]) (some (0,
    5, 3)) (some (0, 5, 3)) (.next ([-1485000000000], [6495000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([-2055000000000], [7740000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-2370000000000], [7830000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-750000000000],
    [2370000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-885000000000], [1335000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4875000000000], [5760000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-7815000000000], [8625000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan44Owner4Part0 : FanWitness := (.next ([4140000000000, -9000000000000], [1245000000000,
    9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([5184000000000, 0], [1620000000000,
    9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([6195000000000, -9000000000000],
    [1995000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2055000000000],
    [750000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([3315000000000], [1995000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([4809000000000], [3006000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([1260000000000], [1245000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([1620000000000], [2880000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([2304000000000], [4500000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([375000000000],
    [5385000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0, 0], [1620000000000,
    9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0, -9000000000000], [2880000000000,
    0]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-201000000000], [5760000000000]) (some (0, 1, 5))
    (some (0, 2, 5)) (.next ([-375000000000], [8190000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-1245000000000, -9000000000000], [5385000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-1620000000000, -9000000000000], [6804000000000, 9000000000000]) (some (0, 2, 5)) (some
    (0, 2, 5)) (.next ([-1995000000000, -9000000000000], [8190000000000, 0]) (some (0, 2, 5)) (some
    (0, 2, 5)) (.next ([-750000000000], [2805000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1995000000000], [5310000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3006000000000],
    [7815000000000]) (some (0, 2, 5)) (some (0, 5, 5)) (.next ([-1245000000000], [2505000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2880000000000], [4500000000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.next ([-4500000000000], [6804000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-5385000000000], [5760000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some
    (0, 5, 4)) (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan45Owner4Part0 : FanWitness := (.next ([5559000000000], [201000000000]) (some (4, 1, 5)) (some
    (4, 1, 5)) (.next ([6570000000000, -9000000000000], [1305000000000, 9000000000000]) (some (4, 1,
    5)) (some (4, 1, 5)) (.next ([4140000000000, -9000000000000], [1245000000000, 9000000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([5184000000000, 0], [1620000000000, 9000000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([3690000000000], [1305000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([5499000000000], [2691000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([1260000000000], [1245000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([1620000000000], [2880000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2304000000000],
    [4500000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([375000000000], [5385000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([315000000000], [7875000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([0, 0], [1620000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1,
    5)) (.next ([0, -9000000000000], [2880000000000, 0]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-201000000000], [5760000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-1305000000000,
    -9000000000000], [7875000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1245000000000,
    -9000000000000], [5385000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1620000000000,
    -9000000000000], [6804000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1305000000000], [4995000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2691000000000],
    [8190000000000]) (some (0, 2, 5)) (some (0, 5, 5)) (.next ([-1245000000000], [2505000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2880000000000], [4500000000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.next ([-4500000000000], [6804000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-5385000000000], [5760000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-7875000000000], [8190000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5,
    4)) (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan47Owner0Part0 : FanWitness := (.next ([-2535000000000], [5415000000000]) (some (1, 9, 7))
    (some (1, 9, 8)) (.next ([-585000000000], [1185000000000]) (some (1, 9, 8)) (some (1, 9, 8))
    (.next ([-375000000000], [750000000000]) (some (1, 9, 8)) (some (1, 9, 8)) (.next
    ([-375000000000], [690000000000]) (some (1, 9, 8)) (some (1, 9, 8)) (.next ([-750000000000],
    [1350000000000]) (some (1, 9, 8)) (some (2, 9, 8)) (.next ([-1185000000000], [2100000000000])
    (some (2, 9, 8)) (some (2, 9, 8)) (.next ([-3855000000000], [6480000000000]) (some (2, 9, 8))
    (some (2, 9, 8)) (.next ([-4275000000000], [6720000000000]) (some (2, 9, 8)) (some (2, 9, 8))
    (.next ([-4470000000000], [6825000000000]) (some (2, 9, 8)) (some (2, 9, 8)) (.next
    ([-5385000000000], [7560000000000]) (some (2, 9, 8)) (some (2, 9, 8)) (.next ([-5625000000000],
    [7380000000000]) (some (2, 9, 8)) (some (2, 9, 8)) (.next ([-6075000000000], [7875000000000])
    (some (2, 9, 8)) (some (2, 9, 8)) (.next ([-5730000000000], [7290000000000]) (some (2, 9, 8))
    (some (2, 9, 8)) (.next ([-4935000000000], [6030000000000]) (some (2, 9, 8)) (some (2, 9, 8))
    (.next ([-6315000000000], [7695000000000]) (some (2, 9, 8)) (some (2, 9, 8)) (.next
    ([-6420000000000], [7605000000000]) (some (2, 9, 8)) (some (2, 9, 8)) (.next ([-1500000000000],
    [1725000000000]) (some (2, 9, 8)) (some (2, 9, 8)) (.next ([-6675000000000], [7290000000000])
    (some (2, 9, 8)) (some (2, 9, 8)) (.next ([-5250000000000], [5655000000000]) (some (2, 9, 8))
    (some (2, 9, 8)) (.next ([-6675000000000], [7125000000000]) (some (2, 9, 8)) (some (2, 9, 8))
    (.next ([-3750000000000], [3930000000000]) (some (2, 9, 8)) (some (2, 9, 8)) (.next
    ([-6915000000000], [7110000000000]) (some (2, 9, 8)) (some (2, 9, 8)) (.next ([-6300000000000],
    [6375000000000]) (some (2, 9, 8)) (some (2, 9, 8)) (.next ([-6915000000000], [6945000000000])
    (some (2, 9, 8)) (some (2, 9, 8)) (.terminal (some (2, 9, 8)) (some (2, 9, 8)) (some (2, 9,
    8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan47Owner0Part1 : FanWitness := (.next ([180000000000], [3750000000000]) (some (0, 3, 6)) (some
    (0, 3, 6)) (.next ([195000000000], [6915000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([75000000000], [6300000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([30000000000],
    [6915000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([0], [165000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-165000000000], [7020000000000]) (some (0, 3, 6)) (some (0, 4, 6))
    (.next ([-195000000000], [4665000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next
    ([-195000000000], [4500000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-345000000000],
    [6540000000000]) (some (0, 4, 6)) (some (0, 9, 6)) (.next ([-540000000000], [6645000000000])
    (some (0, 9, 6)) (some (0, 9, 6)) (.next ([-435000000000], [4500000000000]) (some (0, 9, 6))
    (some (0, 9, 6)) (.next ([-870000000000], [6465000000000]) (some (0, 9, 6)) (some (1, 9, 6))
    (.next ([-810000000000], [5190000000000]) (some (1, 9, 6)) (some (1, 9, 6)) (.next
    ([-270000000000], [1560000000000]) (some (1, 9, 6)) (some (1, 9, 6)) (.next ([-435000000000],
    [1725000000000]) (some (1, 9, 6)) (some (1, 9, 6)) (.next ([-885000000000], [3495000000000])
    (some (1, 9, 6)) (some (1, 9, 6)) (.next ([-1125000000000], [3315000000000]) (some (1, 9, 6))
    (some (1, 9, 6)) (.next ([-1995000000000], [5790000000000]) (some (1, 9, 6)) (some (1, 9, 6))
    (.next ([-2160000000000], [5790000000000]) (some (1, 9, 6)) (some (1, 9, 6)) (.next
    ([-1230000000000], [3225000000000]) (some (1, 9, 6)) (some (1, 9, 6)) (.next ([-375000000000],
    [915000000000]) (some (1, 9, 6)) (some (1, 9, 6)) (.next ([-180000000000], [420000000000]) (some
    (1, 9, 6)) (some (1, 9, 6)) (.next ([-270000000000], [615000000000]) (some (1, 9, 6)) (some (1,
    9, 7)) (.next ([-90000000000], [195000000000]) (some (1, 9, 7)) (some (1, 9, 7))
    fan47Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan47Owner0Part2 : FanWitness := (.next ([540000000000], [375000000000]) (some (0, 2, 9)) (some
    (0, 2, 9)) (.next ([240000000000], [180000000000]) (some (0, 2, 9)) (some (0, 2, 9)) (.next
    ([345000000000], [270000000000]) (some (0, 2, 9)) (some (0, 2, 9)) (.next ([105000000000],
    [90000000000]) (some (0, 2, 9)) (some (0, 2, 9)) (.next ([2880000000000], [2535000000000]) (some
    (0, 2, 9)) (some (0, 2, 9)) (.next ([600000000000], [585000000000]) (some (0, 2, 9)) (some (0,
    2, 9)) (.next ([375000000000], [375000000000]) (some (0, 2, 9)) (some (0, 3, 9)) (.next
    ([315000000000], [375000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([600000000000],
    [750000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([915000000000], [1185000000000]) (some
    (0, 3, 9)) (some (0, 3, 9)) (.next ([2625000000000], [3855000000000]) (some (0, 3, 9)) (some (0,
    3, 9)) (.next ([2445000000000], [4275000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([2355000000000], [4470000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([2175000000000],
    [5385000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([1755000000000], [5625000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([1800000000000], [6075000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([1560000000000], [5730000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([1095000000000], [4935000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([1380000000000], [6315000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([1185000000000],
    [6420000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([225000000000], [1500000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([615000000000], [6675000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([405000000000], [5250000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([450000000000], [6675000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    fan47Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan47Owner6Part0 : FanWitness := (.next ([-15000000000], [4335000000000]) (some (0, 3, 7)) (some
    (0, 4, 7)) (.next ([-15000000000], [735000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next
    ([-30000000000], [750000000000]) (some (0, 4, 7)) (some (1, 4, 7)) (.next ([-495000000000,
    -9000000000000], [5760000000000, 9000000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next
    ([-540000000000], [5250000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-1230000000000,
    -9000000000000], [6480000000000, 9000000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next
    ([-1245000000000, -9000000000000], [6480000000000, 9000000000000]) (some (1, 4, 7)) (some (1, 4,
    7)) (.next ([-2535000000000, 9000000000000], [8280000000000]) (some (1, 4, 7)) (some (1, 4, 7))
    (.next ([-2160000000000, -9000000000000], [5250000000000]) (some (1, 4, 7)) (some (1, 4, 7))
    (.next ([-1620000000000, -9000000000000], [3240000000000, 18000000000000]) (some (1, 4, 7))
    (some (1, 4, 7)) (.next ([-4155000000000], [8280000000000]) (some (1, 4, 7)) (some (1, 4, 7))
    (.next ([-4155000000000], [6660000000000, -9000000000000]) (some (1, 4, 7)) (some (1, 4, 7))
    (.next ([-2520000000000, 9000000000000], [3645000000000, -9000000000000]) (some (1, 4, 7)) (some
    (1, 4, 7)) (.next ([-3570000000000], [4665000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next
    ([-3630000000000, 9000000000000], [4710000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next
    ([-4140000000000], [5265000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-7155000000000],
    [8265000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-7890000000000], [8985000000000])
    (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-7905000000000], [8985000000000]) (some (1, 4, 7))
    (some (1, 4, 7)) (.next ([-3240000000000, 9000000000000], [3630000000000, -9000000000000]) (some
    (1, 4, 7)) (some (1, 4, 7)) (.next ([-3240000000000, 9000000000000], [3615000000000,
    -9000000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-4860000000000], [5250000000000])
    (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-4860000000000], [5235000000000]) (some (1, 4, 7))
    (some (1, 4, 7)) (.next ([-3585000000000], [3600000000000]) (some (1, 4, 7)) (some (1, 4, 7))
    (.terminal (some (1, 4, 7)) (some (1, 4, 7)) (some (1, 4, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan47Owner6Part1 : FanWitness := (.next ([720000000000], [15000000000]) (some (7, 2, 5)) (some
    (7, 2, 5)) (.next ([720000000000], [30000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
    ([5265000000000], [495000000000, 9000000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
    ([4710000000000], [540000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([5250000000000],
    [1230000000000, 9000000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([5235000000000],
    [1245000000000, 9000000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([5745000000000,
    9000000000000], [2535000000000, -9000000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
    ([3090000000000, -9000000000000], [2160000000000, 9000000000000]) (some (7, 2, 5)) (some (7, 2,
    5)) (.next ([1620000000000, 9000000000000], [1620000000000, 9000000000000]) (some (7, 2, 5))
    (some (7, 2, 5)) (.next ([4125000000000], [4155000000000]) (some (7, 2, 5)) (some (7, 2, 5))
    (.next ([2505000000000, -9000000000000], [4155000000000]) (some (7, 2, 5)) (some (7, 2, 5))
    (.next ([1125000000000, 0], [2520000000000, -9000000000000]) (some (7, 2, 5)) (some (7, 2, 7))
    (.next ([1095000000000], [3570000000000]) (some (7, 2, 7)) (some (7, 2, 7)) (.next
    ([1080000000000, 9000000000000], [3630000000000, -9000000000000]) (some (6, 2, 7)) (some (6, 2,
    7)) (.next ([1125000000000], [4140000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
    ([1110000000000], [7155000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([1095000000000],
    [7890000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([1080000000000], [7905000000000])
    (some (6, 2, 7)) (some (6, 2, 7)) (.next ([390000000000, 0], [3240000000000, -9000000000000])
    (some (6, 2, 7)) (some (6, 2, 7)) (.next ([375000000000, 0], [3240000000000, -9000000000000])
    (some (6, 2, 7)) (some (6, 2, 7)) (.next ([390000000000], [4860000000000]) (some (6, 2, 7))
    (some (6, 3, 7)) (.next ([375000000000], [4860000000000]) (some (6, 3, 7)) (some (6, 3, 7))
    (.next ([15000000000], [3585000000000]) (some (6, 3, 7)) (some (6, 3, 7)) (.next ([0],
    [15000000000]) (some (0, 3, 7)) (some (0, 3, 7)) fan47Owner6Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan47Owner6Part2 : FanWitness := (.next ([-15000000000], [4335000000000]) (some (0, 3, 7)) (some
    (0, 4, 7)) (.next ([-15000000000], [735000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next
    ([-30000000000], [750000000000]) (some (0, 4, 7)) (some (1, 4, 7)) (.next ([-495000000000,
    -9000000000000], [5760000000000, 9000000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next
    ([-540000000000], [5250000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-1230000000000,
    -9000000000000], [6480000000000, 9000000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next
    ([-1245000000000, -9000000000000], [6480000000000, 9000000000000]) (some (1, 4, 7)) (some (1, 4,
    7)) (.next ([-2535000000000, 9000000000000], [8280000000000]) (some (1, 4, 7)) (some (1, 4, 7))
    (.next ([-2160000000000, -9000000000000], [5250000000000]) (some (1, 4, 7)) (some (1, 4, 7))
    (.next ([-1620000000000, -9000000000000], [3240000000000, 18000000000000]) (some (1, 4, 7))
    (some (1, 4, 7)) (.next ([-4155000000000], [8280000000000]) (some (1, 4, 7)) (some (1, 4, 7))
    (.next ([-4155000000000], [6660000000000, -9000000000000]) (some (1, 4, 7)) (some (1, 4, 7))
    (.next ([-2520000000000, 9000000000000], [3645000000000, -9000000000000]) (some (1, 4, 7)) (some
    (1, 4, 7)) (.next ([-3630000000000, 9000000000000], [4710000000000]) (some (1, 4, 7)) (some (1,
    4, 7)) (.next ([-3570000000000], [4665000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next
    ([-4140000000000], [5265000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-7155000000000],
    [8265000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-7890000000000], [8985000000000])
    (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-7905000000000], [8985000000000]) (some (1, 4, 7))
    (some (1, 4, 7)) (.next ([-3240000000000, 9000000000000], [3630000000000, -9000000000000]) (some
    (1, 4, 7)) (some (1, 4, 7)) (.next ([-3240000000000, 9000000000000], [3615000000000,
    -9000000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-4860000000000], [5250000000000])
    (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-4860000000000], [5235000000000]) (some (1, 4, 7))
    (some (1, 4, 7)) (.next ([-3585000000000], [3600000000000]) (some (1, 4, 7)) (some (1, 4, 7))
    (.terminal (some (1, 4, 7)) (some (1, 4, 7)) (some (1, 4, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan47Owner6Part3 : FanWitness := (.next ([720000000000], [15000000000]) (some (7, 2, 5)) (some
    (7, 2, 5)) (.next ([720000000000], [30000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
    ([5265000000000], [495000000000, 9000000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
    ([4710000000000], [540000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([5250000000000],
    [1230000000000, 9000000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([5235000000000],
    [1245000000000, 9000000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([5745000000000,
    9000000000000], [2535000000000, -9000000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
    ([3090000000000, -9000000000000], [2160000000000, 9000000000000]) (some (7, 2, 5)) (some (7, 2,
    5)) (.next ([1620000000000, 9000000000000], [1620000000000, 9000000000000]) (some (7, 2, 5))
    (some (7, 2, 5)) (.next ([4125000000000], [4155000000000]) (some (7, 2, 5)) (some (7, 2, 5))
    (.next ([2505000000000, -9000000000000], [4155000000000]) (some (7, 2, 5)) (some (7, 2, 5))
    (.next ([1125000000000, 0], [2520000000000, -9000000000000]) (some (7, 2, 5)) (some (7, 2, 7))
    (.next ([1080000000000, 9000000000000], [3630000000000, -9000000000000]) (some (7, 2, 7)) (some
    (7, 2, 7)) (.next ([1095000000000], [3570000000000]) (some (7, 2, 7)) (some (7, 2, 7)) (.next
    ([1125000000000], [4140000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([1110000000000],
    [7155000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([1095000000000], [7890000000000])
    (some (6, 2, 7)) (some (6, 2, 7)) (.next ([1080000000000], [7905000000000]) (some (6, 2, 7))
    (some (6, 2, 7)) (.next ([390000000000, 0], [3240000000000, -9000000000000]) (some (6, 2, 7))
    (some (6, 2, 7)) (.next ([375000000000, 0], [3240000000000, -9000000000000]) (some (6, 2, 7))
    (some (6, 2, 7)) (.next ([390000000000], [4860000000000]) (some (6, 2, 7)) (some (6, 3, 7))
    (.next ([375000000000], [4860000000000]) (some (6, 3, 7)) (some (6, 3, 7)) (.next
    ([15000000000], [3585000000000]) (some (6, 3, 7)) (some (6, 3, 7)) (.next ([0], [15000000000])
    (some (0, 3, 7)) (some (0, 3, 7)) fan47Owner6Part2))))))))))))))))))))))))

theorem excluded40_0 : ExcludedOn (model40.B 0 ++ [step40.q]) 9000000000000 (model40.caps 0)
    (model40.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_1 : ExcludedOn (model40.B 1 ++ [step40.q]) 9000000000000 (model40.caps 1)
    (model40.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_2 : ExcludedOn (model40.B 2 ++ [step40.q]) 9000000000000 (model40.caps 2)
    (model40.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_3 : ExcludedOn (model40.B 3 ++ [step40.q]) 9000000000000 (model40.caps 3)
    (model40.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_4 : ExcludedOn (model40.B 4 ++ [step40.q]) 9000000000000 (model40.caps 4)
    (model40.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_5 : ExcludedOn (model40.B 5 ++ [step40.q]) 9000000000000 (model40.caps 5)
    (model40.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3726000000000], [9000000000]) (some (3, 0, 5))
      (some (3, 1, 5)) fan40Owner5Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_7 : ExcludedOn (model40.B 7 ++ [step40.q]) 9000000000000 (model40.caps 7)
    (model40.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_8 : ExcludedOn (model40.B 8 ++ [step40.q]) 9000000000000 (model40.caps 8)
    (model40.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_9 : ExcludedOn (model40.B 9 ++ [step40.q]) 9000000000000 (model40.caps 9)
    (model40.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2520000000000], [375000000000]) (some (5, 0, 1))
      (some (5, 1, 2)) (.next ([3390000000000], [945000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([240000000000], [135000000000]) (some (5, 1, 2)) (some (5, 1, 2)) fan40Owner9Part0))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem checked40 : StepValid model40 9000000000000 step40 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded40_0
    · exact excluded40_1
    · exact excluded40_2
    · exact excluded40_3
    · exact excluded40_4
    · exact excluded40_5
    · exact (hj rfl).elim
    · exact excluded40_7
    · exact excluded40_8
    · exact excluded40_9
theorem next40 : model40.insert step40 = model41 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded41_0 : ExcludedOn (model41.B 0 ++ [step41.q]) 9000000000000 (model41.caps 0)
    (model41.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_2 : ExcludedOn (model41.B 2 ++ [step41.q]) 9000000000000 (model41.caps 2)
    (model41.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_3 : ExcludedOn (model41.B 3 ++ [step41.q]) 9000000000000 (model41.caps 3)
    (model41.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_4 : ExcludedOn (model41.B 4 ++ [step41.q]) 9000000000000 (model41.caps 4)
    (model41.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_5 : ExcludedOn (model41.B 5 ++ [step41.q]) 9000000000000 (model41.caps 5)
    (model41.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_6 : ExcludedOn (model41.B 6 ++ [step41.q]) 9000000000000 (model41.caps 6)
    (model41.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_7 : ExcludedOn (model41.B 7 ++ [step41.q]) 9000000000000 (model41.caps 7)
    (model41.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_8 : ExcludedOn (model41.B 8 ++ [step41.q]) 9000000000000 (model41.caps 8)
    (model41.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_9 : ExcludedOn (model41.B 9 ++ [step41.q]) 9000000000000 (model41.caps 9)
    (model41.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked41 : StepValid model41 9000000000000 step41 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded41_0
    · exact (hj rfl).elim
    · exact excluded41_2
    · exact excluded41_3
    · exact excluded41_4
    · exact excluded41_5
    · exact excluded41_6
    · exact excluded41_7
    · exact excluded41_8
    · exact excluded41_9
theorem next41 : model41.insert step41 = model42 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded42_0 : ExcludedOn (model42.B 0 ++ [step42.q]) 9000000000000 (model42.caps 0)
    (model42.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_1 : ExcludedOn (model42.B 1 ++ [step42.q]) 9000000000000 (model42.caps 1)
    (model42.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_2 : ExcludedOn (model42.B 2 ++ [step42.q]) 9000000000000 (model42.caps 2)
    (model42.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_3 : ExcludedOn (model42.B 3 ++ [step42.q]) 9000000000000 (model42.caps 3)
    (model42.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_4 : ExcludedOn (model42.B 4 ++ [step42.q]) 9000000000000 (model42.caps 4)
    (model42.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5559000000000], [201000000000]) (some (3, 0, 2))
      (some (3, 4, 2)) (.next ([4140000000000, -9000000000000], [1245000000000, 9000000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([5184000000000, 0], [1620000000000, 9000000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([5184000000000], [3666000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([2094000000000], [3291000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([375000000000], [5385000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0, 0],
      [1620000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-201000000000],
      [5760000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1245000000000, -9000000000000],
      [5385000000000, 0]) (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-1620000000000,
      -9000000000000], [6804000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-3666000000000], [8850000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-3291000000000], [5385000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-5385000000000], [5760000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded42_6 : ExcludedOn (model42.B 6 ++ [step42.q]) 9000000000000 (model42.caps 6)
    (model42.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_7 : ExcludedOn (model42.B 7 ++ [step42.q]) 9000000000000 (model42.caps 7)
    (model42.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_8 : ExcludedOn (model42.B 8 ++ [step42.q]) 9000000000000 (model42.caps 8)
    (model42.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_9 : ExcludedOn (model42.B 9 ++ [step42.q]) 9000000000000 (model42.caps 9)
    (model42.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked42 : StepValid model42 9000000000000 step42 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded42_0
    · exact excluded42_1
    · exact excluded42_2
    · exact excluded42_3
    · exact excluded42_4
    · exact (hj rfl).elim
    · exact excluded42_6
    · exact excluded42_7
    · exact excluded42_8
    · exact excluded42_9
theorem next42 : model42.insert step42 = model43 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded43_0 : ExcludedOn (model43.B 0 ++ [step43.q]) 9000000000000 (model43.caps 0)
    (model43.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 7 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_1 : ExcludedOn (model43.B 1 ++ [step43.q]) 9000000000000 (model43.caps 1)
    (model43.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_2 : ExcludedOn (model43.B 2 ++ [step43.q]) 9000000000000 (model43.caps 2)
    (model43.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_3 : ExcludedOn (model43.B 3 ++ [step43.q]) 9000000000000 (model43.caps 3)
    (model43.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_5 : ExcludedOn (model43.B 5 ++ [step43.q]) 9000000000000 (model43.caps 5)
    (model43.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4860000000000], [414000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([5334000000000, 0], [1620000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([3240000000000, -9000000000000], [2034000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2106000000000], [1980000000000]) (some (4, 1, 2))
      (some (4, 1, 3)) (.next ([2880000000000], [4500000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([834000000000], [2046000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([1260000000000, -9000000000000], [6120000000000, 9000000000000]) (some (0, 1, 3)) (some (0,
      1, 3)) (.next ([60000000000], [4860000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [5334000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-414000000000], [5274000000000])
      (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-1620000000000, -9000000000000], [6954000000000,
      9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2034000000000, -9000000000000],
      [5274000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1980000000000], [4086000000000])
      (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-4500000000000], [7380000000000]) (some (0, 2, 3))
      (some (0, 2, 4)) (.next ([-2046000000000], [2880000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-6120000000000, -9000000000000], [7380000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-4860000000000], [4920000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded43_6 : ExcludedOn (model43.B 6 ++ [step43.q]) 9000000000000 (model43.caps 6)
    (model43.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_7 : ExcludedOn (model43.B 7 ++ [step43.q]) 9000000000000 (model43.caps 7)
    (model43.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_8 : ExcludedOn (model43.B 8 ++ [step43.q]) 9000000000000 (model43.caps 8)
    (model43.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_9 : ExcludedOn (model43.B 9 ++ [step43.q]) 9000000000000 (model43.caps 9)
    (model43.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked43 : StepValid model43 9000000000000 step43 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded43_0
    · exact excluded43_1
    · exact excluded43_2
    · exact excluded43_3
    · exact (hj rfl).elim
    · exact excluded43_5
    · exact excluded43_6
    · exact excluded43_7
    · exact excluded43_8
    · exact excluded43_9
theorem next43 : model43.insert step43 = model44 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded44_1 : ExcludedOn (model44.B 1 ++ [step44.q]) 9000000000000 (model44.caps 1)
    (model44.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_2 : ExcludedOn (model44.B 2 ++ [step44.q]) 9000000000000 (model44.caps 2)
    (model44.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_3 : ExcludedOn (model44.B 3 ++ [step44.q]) 9000000000000 (model44.caps 3)
    (model44.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (101) (834) (83400) (.witnessedFan (.next ([750000000000,
      -9000000000000], [0, 9000000000000]) (some (3, 0, 5)) (some (4, 0, 5)) (.next ([7005000000000,
      -9000000000000], [810000000000, 9000000000000]) (some (4, 0, 5)) (some (4, 1, 5)) (.next
      ([5760000000000], [735000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      fan44Owner3Part0)))) (.split (15857) (125100) (130938) (13093800) (.witnessedFan (.next
      ([750000000000, -9000000000000], [0, 9000000000000]) (some (3, 0, 5)) (some (4, 0, 5)) (.next
      ([7005000000000, -9000000000000], [810000000000, 9000000000000]) (some (4, 0, 5)) (some (4, 1,
      5)) (.next ([6255000000000], [810000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      fan44Owner3Part1)))) (.witnessedFan (.next ([6255000000000], [810000000000]) (some (3, 0, 5))
      (some (4, 0, 5)) (.next ([7005000000000, -9000000000000], [810000000000, 9000000000000]) (some
      (4, 0, 5)) (some (4, 0, 5)) (.next ([750000000000, -9000000000000], [0, 9000000000000]) (some
      (4, 0, 5)) (some (4, 5, 5)) fan44Owner3Part2)))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded44_4 : ExcludedOn (model44.B 4 ++ [step44.q]) 9000000000000 (model44.caps 4)
    (model44.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2880000000000, -9000000000000], [0,
      9000000000000]) (some (4, 0, 5)) (some (4, 1, 5)) (.next ([5559000000000], [201000000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([7815000000000], [375000000000]) (some (4, 1, 5))
      (some (4, 1, 5)) fan44Owner4Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded44_5 : ExcludedOn (model44.B 5 ++ [step44.q]) 9000000000000 (model44.caps 5)
    (model44.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4860000000000], [414000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([8190000000000], [1185000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([3330000000000], [771000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([5334000000000, 0], [1620000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([6570000000000, -9000000000000], [2805000000000, 9000000000000]) (some (4, 1, 2)) (some (4,
      1, 2)) (.next ([3240000000000, -9000000000000], [2034000000000, 9000000000000]) (some (4, 1,
      2)) (some (4, 1, 4)) (.next ([4149000000000], [4041000000000]) (some (4, 1, 4)) (some (4, 1,
      4)) (.next ([60000000000], [4860000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [5334000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-414000000000], [5274000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1185000000000], [9375000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-771000000000], [4101000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-1620000000000, -9000000000000], [6954000000000, 9000000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2805000000000, -9000000000000], [9375000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2034000000000, -9000000000000], [5274000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-4041000000000], [8190000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-4860000000000], [4920000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded44_6 : ExcludedOn (model44.B 6 ++ [step44.q]) 9000000000000 (model44.caps 6)
    (model44.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_7 : ExcludedOn (model44.B 7 ++ [step44.q]) 9000000000000 (model44.caps 7)
    (model44.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_8 : ExcludedOn (model44.B 8 ++ [step44.q]) 9000000000000 (model44.caps 8)
    (model44.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_9 : ExcludedOn (model44.B 9 ++ [step44.q]) 9000000000000 (model44.caps 9)
    (model44.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked44 : StepValid model44 9000000000000 step44 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded44_1
    · exact excluded44_2
    · exact excluded44_3
    · exact excluded44_4
    · exact excluded44_5
    · exact excluded44_6
    · exact excluded44_7
    · exact excluded44_8
    · exact excluded44_9
theorem next44 : model44.insert step44 = model45 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded45_1 : ExcludedOn (model45.B 1 ++ [step45.q]) 9000000000000 (model45.caps 1)
    (model45.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_2 : ExcludedOn (model45.B 2 ++ [step45.q]) 9000000000000 (model45.caps 2)
    (model45.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_3 : ExcludedOn (model45.B 3 ++ [step45.q]) 9000000000000 (model45.caps 3)
    (model45.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([750000000000, -9000000000000], [0,
      9000000000000]) (some (3, 0, 5)) (some (4, 0, 5)) (.next ([5760000000000], [735000000000,
      9000000000000]) (some (4, 0, 5)) (some (4, 5, 5)) (.next ([6210000000000], [1620000000000,
      9000000000000]) (some (4, 5, 5)) (some (4, 5, 5)) (.next ([5010000000000], [1485000000000])
      (some (4, 5, 5)) (some (4, 5, 3)) (.next ([6000000000000], [2430000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([5460000000000], [2370000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([1620000000000], [750000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([450000000000], [885000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([885000000000],
      [4875000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([1125000000000], [8190000000000])
      (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0], [1620000000000, 9000000000000]) (some (4, 5,
      3)) (some (4, 5, 3)) (.next ([0, -9000000000000], [750000000000]) (some (0, 5, 3)) (some (0,
      5, 3)) (.next ([-735000000000, -9000000000000], [6495000000000, 9000000000000]) (some (0, 5,
      3)) (some (0, 5, 3)) (.next ([-1620000000000, -9000000000000], [7830000000000, 9000000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1485000000000], [6495000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-2430000000000], [8430000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-2370000000000], [7830000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-750000000000], [2370000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-885000000000],
      [1335000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4875000000000], [5760000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-8190000000000], [9315000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5,
      3))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded45_4 : ExcludedOn (model45.B 4 ++ [step45.q]) 9000000000000 (model45.caps 4)
    (model45.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2880000000000, -9000000000000], [0,
      9000000000000]) (some (4, 0, 5)) (some (4, 1, 5)) fan45Owner4Part0)) (den := 9000000000000)
      (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded45_5 : ExcludedOn (model45.B 5 ++ [step45.q]) 9000000000000 (model45.caps 5)
    (model45.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4860000000000], [414000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([7875000000000], [810000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([3015000000000], [396000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([5334000000000, 0], [1620000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([6255000000000, -9000000000000], [2430000000000, 9000000000000]) (some (4, 1, 2)) (some (4,
      1, 2)) (.next ([3240000000000, -9000000000000], [2034000000000, 9000000000000]) (some (4, 1,
      2)) (some (4, 1, 4)) (.next ([4524000000000], [3351000000000]) (some (4, 1, 4)) (some (4, 1,
      4)) (.next ([60000000000], [4860000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [5334000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-414000000000], [5274000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-810000000000], [8685000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-396000000000], [3411000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-1620000000000, -9000000000000], [6954000000000, 9000000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2430000000000, -9000000000000], [8685000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2034000000000, -9000000000000], [5274000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-3351000000000], [7875000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-4860000000000], [4920000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded45_6 : ExcludedOn (model45.B 6 ++ [step45.q]) 9000000000000 (model45.caps 6)
    (model45.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_7 : ExcludedOn (model45.B 7 ++ [step45.q]) 9000000000000 (model45.caps 7)
    (model45.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_8 : ExcludedOn (model45.B 8 ++ [step45.q]) 9000000000000 (model45.caps 8)
    (model45.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_9 : ExcludedOn (model45.B 9 ++ [step45.q]) 9000000000000 (model45.caps 9)
    (model45.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked45 : StepValid model45 9000000000000 step45 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded45_1
    · exact excluded45_2
    · exact excluded45_3
    · exact excluded45_4
    · exact excluded45_5
    · exact excluded45_6
    · exact excluded45_7
    · exact excluded45_8
    · exact excluded45_9
theorem next45 : model45.insert step45 = model46 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded46_1 : ExcludedOn (model46.B 1 ++ [step46.q]) 9000000000000 (model46.caps 1)
    (model46.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5760000000000], [2250000000000]) none none
      (.next ([4140000000000, -9000000000000], [2250000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([2370000000000, 0], [1620000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([120000000000], [8010000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [1620000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2250000000000],
      [8010000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2250000000000, 0],
      [6390000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1620000000000,
      -9000000000000], [3990000000000, 9000000000000]) (some (3, 1, 0)) (some (3, 1, 3)) (.next
      ([-8010000000000], [8130000000000]) (some (3, 1, 3)) none (.terminal none none none)))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded46_2 : ExcludedOn (model46.B 2 ++ [step46.q]) 9000000000000 (model46.caps 2)
    (model46.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7380000000000, -9000000000000], [1620000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2250000000000], [990000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4140000000000, -9000000000000], [2250000000000, 0])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([630000000000, -9000000000000], [2610000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [1620000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-1620000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-990000000000],
      [3240000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2250000000000, 0],
      [6390000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2610000000000,
      -9000000000000], [3240000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded46_3 : ExcludedOn (model46.B 3 ++ [step46.q]) 9000000000000 (model46.caps 3)
    (model46.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_4 : ExcludedOn (model46.B 4 ++ [step46.q]) 9000000000000 (model46.caps 4)
    (model46.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_5 : ExcludedOn (model46.B 5 ++ [step46.q]) 9000000000000 (model46.caps 5)
    (model46.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_6 : ExcludedOn (model46.B 6 ++ [step46.q]) 9000000000000 (model46.caps 6)
    (model46.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_7 : ExcludedOn (model46.B 7 ++ [step46.q]) 9000000000000 (model46.caps 7)
    (model46.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_8 : ExcludedOn (model46.B 8 ++ [step46.q]) 9000000000000 (model46.caps 8)
    (model46.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_9 : ExcludedOn (model46.B 9 ++ [step46.q]) 9000000000000 (model46.caps 9)
    (model46.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked46 : StepValid model46 9000000000000 step46 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded46_1
    · exact excluded46_2
    · exact excluded46_3
    · exact excluded46_4
    · exact excluded46_5
    · exact excluded46_6
    · exact excluded46_7
    · exact excluded46_8
    · exact excluded46_9
theorem next46 : model46.insert step46 = model47 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded47_0 : ExcludedOn (model47.B 0 ++ [step47.q]) 9000000000000 (model47.caps 0)
    (model47.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6855000000000], [165000000000]) (some (8, 2, 9))
      (some (8, 2, 9)) (.next ([4470000000000], [195000000000]) (some (8, 2, 9)) (some (8, 2, 9))
      (.next ([4305000000000], [195000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next
      ([6195000000000], [345000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next ([6105000000000],
      [540000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next ([4065000000000], [435000000000])
      (some (8, 2, 9)) (some (8, 2, 9)) (.next ([5595000000000], [870000000000]) (some (8, 2, 9))
      (some (8, 2, 9)) (.next ([4380000000000], [810000000000]) (some (8, 2, 9)) (some (8, 2, 9))
      (.next ([1290000000000], [270000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next
      ([1290000000000], [435000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next ([2610000000000],
      [885000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next ([2190000000000], [1125000000000])
      (some (8, 2, 9)) (some (8, 2, 9)) (.next ([3795000000000], [1995000000000]) (some (8, 2, 9))
      (some (8, 2, 9)) (.next ([3630000000000], [2160000000000]) (some (8, 2, 9)) (some (8, 2, 9))
      (.next ([1995000000000], [1230000000000]) (some (8, 2, 9)) (some (8, 2, 9))
      fan47Owner0Part2))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded47_2 : ExcludedOn (model47.B 2 ++ [step47.q]) 9000000000000 (model47.caps 2)
    (model47.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7380000000000, -9000000000000], [1620000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2535000000000, -9000000000000],
      [2340000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([3255000000000,
      -9000000000000], [6465000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0,
      0], [1620000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-1620000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 3, 1)) (some (0, 3, 2)) (.next
      ([-2340000000000, -9000000000000], [4875000000000, 0]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-6465000000000, -9000000000000], [9720000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.terminal (some (0, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded47_3 : ExcludedOn (model47.B 3 ++ [step47.q]) 9000000000000 (model47.caps 3)
    (model47.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_4 : ExcludedOn (model47.B 4 ++ [step47.q]) 9000000000000 (model47.caps 4)
    (model47.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_5 : ExcludedOn (model47.B 5 ++ [step47.q]) 9000000000000 (model47.caps 5)
    (model47.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_6 : ExcludedOn (model47.B 6 ++ [step47.q]) 9000000000000 (model47.caps 6)
    (model47.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (265) (933) (93300) (.witnessedFan (.next ([4320000000000],
      [15000000000]) (some (7, 1, 4)) (some (7, 2, 5)) fan47Owner6Part1)) (.witnessedFan (.next
      ([4320000000000], [15000000000]) (some (7, 1, 4)) (some (7, 2, 5)) fan47Owner6Part3))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded47_7 : ExcludedOn (model47.B 7 ++ [step47.q]) 9000000000000 (model47.caps 7)
    (model47.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_8 : ExcludedOn (model47.B 8 ++ [step47.q]) 9000000000000 (model47.caps 8)
    (model47.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_9 : ExcludedOn (model47.B 9 ++ [step47.q]) 9000000000000 (model47.caps 9)
    (model47.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked47 : StepValid model47 9000000000000 step47 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded47_0
    · exact (hj rfl).elim
    · exact excluded47_2
    · exact excluded47_3
    · exact excluded47_4
    · exact excluded47_5
    · exact excluded47_6
    · exact excluded47_7
    · exact excluded47_8
    · exact excluded47_9
theorem next47 : model47.insert step47 = model48 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint180000190000
end ConwaySoifer.Simplified.Certificates
