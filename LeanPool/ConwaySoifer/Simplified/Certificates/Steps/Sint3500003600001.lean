/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint350000360000
import Mathlib.Tactic.FinCases

/-!
# Sint 350000 360000 1

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
namespace Sint350000360000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan9Owner0Part0 : FanWitness := (.next ([-1194000000000, -3840000000000], [5397000000000,
    1920000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([-897000000000, -1920000000000],
    [3828000000000, -1920000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([-150000000000],
    [450000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([-4995000000000], [10170000000000])
    (some (8, 2, 4)) (some (8, 2, 4)) (.next ([-5025000000000], [10125000000000]) (some (8, 2, 4))
    (some (8, 2, 4)) (.next ([-672000000000, -1920000000000], [1344000000000, 3840000000000]) (some
    (8, 2, 4)) (some (8, 2, 4)) (.next ([-5100000000000], [9825000000000]) (some (8, 2, 4)) (some
    (8, 3, 4)) (.next ([-4950000000000], [9375000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next
    ([-45000000000], [75000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next ([-4098000000000,
    1920000000000], [6342000000000, 1920000000000]) (some (8, 3, 4)) (some (8, 3, 5)) (.next
    ([-4128000000000, 1920000000000], [6297000000000, 1920000000000]) (some (8, 3, 5)) (some (8, 3,
    5)) (.next ([-4203000000000, 1920000000000], [5997000000000, 1920000000000]) (some (8, 3, 5))
    (some (8, 3, 5)) (.next ([-4053000000000, 1920000000000], [5547000000000, 1920000000000]) (some
    (8, 3, 5)) (some (8, 3, 5)) (.next ([-345000000000], [450000000000]) (some (8, 3, 5)) (some (8,
    3, 5)) (.next ([-3828000000000, 1920000000000], [4947000000000, 1920000000000]) (some (8, 3, 5))
    (some (8, 3, 5)) (.next ([-5442000000000, -1920000000000], [7014000000000, 3840000000000]) (some
    (8, 3, 5)) (some (8, 3, 5)) (.next ([-5472000000000, -1920000000000], [6969000000000,
    3840000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-300000000000], [375000000000]) (some
    (8, 3, 5)) (some (8, 3, 5)) (.next ([-5547000000000, -1920000000000], [6669000000000,
    3840000000000]) (some (8, 3, 5)) (some (8, 3, 6)) (.next ([-5397000000000, -1920000000000],
    [6219000000000, 3840000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-3156000000000,
    3840000000000], [3603000000000, -1920000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
    ([-5172000000000, -1920000000000], [5619000000000, 3840000000000]) (some (8, 3, 6)) (some (8, 3,
    6)) (.next ([-6114000000000, -3840000000000], [6342000000000, 1920000000000]) (some (8, 3, 6))
    (some (8, 3, 6)) (.next ([-6144000000000, -3840000000000], [6297000000000, 1920000000000]) (some
    (8, 3, 6)) (some (8, 3, 6)) (.terminal (some (8, 3, 6)) (some (8, 3, 6)) (some (8, 3,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan9Owner0Part1 : FanWitness := (.next ([4425000000000], [4950000000000]) (some (7, 8, 4)) (some
    (7, 8, 4)) (.next ([30000000000], [45000000000]) (some (7, 8, 4)) (some (8, 8, 4)) (.next
    ([2244000000000, 3840000000000], [4098000000000, -1920000000000]) (some (8, 8, 4)) (some (8, 8,
    4)) (.next ([2169000000000, 3840000000000], [4128000000000, -1920000000000]) (some (8, 8, 4))
    (some (8, 8, 4)) (.next ([1794000000000, 3840000000000], [4203000000000, -1920000000000]) (some
    (8, 8, 4)) (some (8, 8, 4)) (.next ([1494000000000, 3840000000000], [4053000000000,
    -1920000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next ([105000000000], [345000000000]) (some
    (8, 8, 4)) (some (8, 8, 4)) (.next ([1119000000000, 3840000000000], [3828000000000,
    -1920000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next ([1572000000000, 1920000000000],
    [5442000000000, 1920000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([1497000000000,
    1920000000000], [5472000000000, 1920000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
    ([75000000000], [300000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([1122000000000,
    1920000000000], [5547000000000, 1920000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
    ([822000000000, 1920000000000], [5397000000000, 1920000000000]) (some (8, 2, 4)) (some (8, 2,
    4)) (.next ([447000000000, 1920000000000], [3156000000000, -3840000000000]) (some (8, 2, 4))
    (some (8, 2, 4)) (.next ([447000000000, 1920000000000], [5172000000000, 1920000000000]) (some
    (8, 2, 4)) (some (8, 2, 4)) (.next ([228000000000, -1920000000000], [6114000000000,
    3840000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([153000000000, -1920000000000],
    [6144000000000, 3840000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([0, 0],
    [2016000000000, 5760000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([-222000000000,
    -1920000000000], [6219000000000, 3840000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
    ([-45000000000], [795000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([-444000000000,
    -3840000000000], [5442000000000, 1920000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
    ([-522000000000, -1920000000000], [6069000000000, 3840000000000]) (some (8, 2, 4)) (some (8, 2,
    4)) (.next ([-519000000000, -3840000000000], [5472000000000, 1920000000000]) (some (8, 2, 4))
    (some (8, 2, 4)) (.next ([-894000000000, -3840000000000], [5547000000000, 1920000000000]) (some
    (8, 2, 4)) (some (8, 2, 4)) fan9Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan13Owner0Part0 : FanWitness := (.next ([-444000000000, -3840000000000], [5442000000000,
    1920000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next ([-522000000000, -1920000000000],
    [6069000000000, 3840000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next ([-519000000000,
    -3840000000000], [5472000000000, 1920000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next
    ([-456000000000, 3840000000000], [3828000000000, -1920000000000]) (some (8, 8, 4)) (some (8, 8,
    4)) (.next ([-894000000000, -3840000000000], [5547000000000, 1920000000000]) (some (8, 2, 4))
    (some (8, 2, 4)) (.next ([-1128000000000, 1920000000000], [5172000000000, 1920000000000]) (some
    (8, 2, 4)) (some (8, 2, 4)) (.next ([-1194000000000, -3840000000000], [5397000000000,
    1920000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([-150000000000], [450000000000]) (some
    (8, 2, 4)) (some (8, 2, 4)) (.next ([-1128000000000, 1920000000000], [3156000000000,
    -3840000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([-672000000000, -1920000000000],
    [1344000000000, 3840000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([-45000000000],
    [75000000000]) (some (8, 2, 4)) (some (8, 3, 4)) (.next ([-4098000000000, 1920000000000],
    [6342000000000, 1920000000000]) (some (8, 3, 4)) (some (8, 3, 5)) (.next ([-6600000000000],
    [10125000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-6675000000000], [9825000000000])
    (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-6525000000000], [9375000000000]) (some (8, 3, 5))
    (some (8, 3, 5)) (.next ([-4053000000000, 1920000000000], [5547000000000, 1920000000000]) (some
    (8, 3, 5)) (some (8, 3, 5)) (.next ([-345000000000], [450000000000]) (some (8, 3, 5)) (some (8,
    3, 5)) (.next ([-5442000000000, -1920000000000], [7014000000000, 3840000000000]) (some (8, 3,
    5)) (some (8, 3, 5)) (.next ([-5472000000000, -1920000000000], [6969000000000, 3840000000000])
    (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-300000000000], [375000000000]) (some (8, 3, 5))
    (some (8, 3, 5)) (.next ([-5547000000000, -1920000000000], [6669000000000, 3840000000000]) (some
    (8, 3, 5)) (some (8, 3, 6)) (.next ([-5397000000000, -1920000000000], [6219000000000,
    3840000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-6114000000000, -3840000000000],
    [6342000000000, 1920000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-6144000000000,
    -3840000000000], [6297000000000, 1920000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.terminal
    (some (8, 3, 6)) (some (8, 3, 6)) (some (8, 3, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan13Owner0Part1 : FanWitness := (.next ([3372000000000, 1920000000000], [456000000000,
    -3840000000000]) (some (6, 8, 4)) (some (6, 8, 4)) (.next ([4653000000000, -1920000000000],
    [894000000000, 3840000000000]) (some (6, 8, 4)) (some (6, 8, 4)) (.next ([4044000000000,
    3840000000000], [1128000000000, -1920000000000]) (some (6, 8, 4)) (some (6, 8, 4)) (.next
    ([4203000000000, -1920000000000], [1194000000000, 3840000000000]) (some (6, 8, 4)) (some (6, 8,
    4)) (.next ([300000000000], [150000000000]) (some (6, 8, 4)) (some (6, 8, 4)) (.next
    ([2028000000000, -1920000000000], [1128000000000, -1920000000000]) (some (6, 8, 4)) (some (7, 8,
    4)) (.next ([672000000000, 1920000000000], [672000000000, 1920000000000]) (some (7, 8, 4)) (some
    (7, 8, 4)) (.next ([30000000000], [45000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next
    ([2244000000000, 3840000000000], [4098000000000, -1920000000000]) (some (7, 8, 4)) (some (7, 8,
    4)) (.next ([3525000000000], [6600000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next
    ([3150000000000], [6675000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([2850000000000],
    [6525000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([1494000000000, 3840000000000],
    [4053000000000, -1920000000000]) (some (7, 8, 4)) (some (8, 8, 4)) (.next ([105000000000],
    [345000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next ([1572000000000, 1920000000000],
    [5442000000000, 1920000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next ([1497000000000,
    1920000000000], [5472000000000, 1920000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next
    ([75000000000], [300000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next ([1122000000000,
    1920000000000], [5547000000000, 1920000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next
    ([822000000000, 1920000000000], [5397000000000, 1920000000000]) (some (8, 8, 4)) (some (8, 8,
    4)) (.next ([228000000000, -1920000000000], [6114000000000, 3840000000000]) (some (8, 8, 4))
    (some (8, 8, 4)) (.next ([153000000000, -1920000000000], [6144000000000, 3840000000000]) (some
    (8, 8, 4)) (some (8, 8, 4)) (.next ([0, 0], [2016000000000, 5760000000000]) (some (8, 8, 4))
    (some (8, 8, 4)) (.next ([-222000000000, -1920000000000], [6219000000000, 3840000000000]) (some
    (8, 8, 4)) (some (8, 8, 4)) (.next ([-45000000000], [795000000000]) (some (8, 8, 4)) (some (8,
    8, 4)) fan13Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner0Part0 : FanWitness := (.next ([-894000000000, -3840000000000], [5547000000000,
    1920000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([-1875000000000], [9645000000000])
    (some (0, 8, 4)) (some (0, 8, 4)) (.next ([-1950000000000], [9675000000000]) (some (0, 8, 4))
    (some (0, 8, 4)) (.next ([-1194000000000, -3840000000000], [5397000000000, 1920000000000]) (some
    (0, 8, 4)) (some (0, 8, 4)) (.next ([-2325000000000], [9750000000000]) (some (0, 8, 4)) (some
    (0, 8, 4)) (.next ([-2625000000000], [9600000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next
    ([-150000000000], [450000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([-672000000000,
    -1920000000000], [1344000000000, 3840000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next
    ([-2103000000000, 1920000000000], [3531000000000, -3840000000000]) (some (0, 8, 4)) (some (1, 8,
    4)) (.next ([-45000000000], [75000000000]) (some (1, 8, 4)) (some (1, 8, 4)) (.next
    ([-4098000000000, 1920000000000], [6342000000000, 1920000000000]) (some (1, 8, 4)) (some (1, 8,
    5)) (.next ([-4128000000000, 1920000000000], [6297000000000, 1920000000000]) (some (1, 8, 5))
    (some (1, 8, 5)) (.next ([-4203000000000, 1920000000000], [5997000000000, 1920000000000]) (some
    (1, 8, 5)) (some (1, 8, 5)) (.next ([-4053000000000, 1920000000000], [5547000000000,
    1920000000000]) (some (1, 8, 5)) (some (1, 8, 5)) (.next ([-4119000000000, -3840000000000],
    [5547000000000, 1920000000000]) (some (1, 8, 5)) (some (1, 8, 5)) (.next ([-345000000000],
    [450000000000]) (some (1, 8, 5)) (some (1, 8, 5)) (.next ([-5442000000000, -1920000000000],
    [7014000000000, 3840000000000]) (some (1, 8, 5)) (some (1, 8, 5)) (.next ([-5472000000000,
    -1920000000000], [6969000000000, 3840000000000]) (some (1, 8, 5)) (some (1, 8, 5)) (.next
    ([-300000000000], [375000000000]) (some (1, 8, 5)) (some (1, 8, 5)) (.next ([-3447000000000,
    -1920000000000], [4203000000000, -1920000000000]) (some (1, 8, 5)) (some (1, 8, 6)) (.next
    ([-5547000000000, -1920000000000], [6669000000000, 3840000000000]) (some (1, 8, 6)) (some (8, 8,
    6)) (.next ([-5397000000000, -1920000000000], [6219000000000, 3840000000000]) (some (8, 8, 6))
    (some (8, 8, 6)) (.next ([-6114000000000, -3840000000000], [6342000000000, 1920000000000]) (some
    (8, 8, 6)) (some (8, 8, 6)) (.next ([-6144000000000, -3840000000000], [6297000000000,
    1920000000000]) (some (8, 8, 6)) (some (8, 8, 6)) (.terminal (some (8, 8, 6)) (some (8, 8, 6))
    (some (8, 8, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner0Part1 : FanWitness := (.next ([300000000000], [150000000000]) (some (6, 8, 4)) (some
    (6, 8, 4)) (.next ([672000000000, 1920000000000], [672000000000, 1920000000000]) (some (6, 8,
    4)) (some (7, 8, 4)) (.next ([1428000000000, -1920000000000], [2103000000000, -1920000000000])
    (some (7, 8, 4)) (some (7, 8, 4)) (.next ([30000000000], [45000000000]) (some (7, 8, 4)) (some
    (7, 8, 4)) (.next ([2244000000000, 3840000000000], [4098000000000, -1920000000000]) (some (7, 8,
    4)) (some (7, 8, 4)) (.next ([2169000000000, 3840000000000], [4128000000000, -1920000000000])
    (some (7, 8, 4)) (some (7, 8, 4)) (.next ([1794000000000, 3840000000000], [4203000000000,
    -1920000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([1494000000000, 3840000000000],
    [4053000000000, -1920000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([1428000000000,
    -1920000000000], [4119000000000, 3840000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next
    ([105000000000], [345000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([1572000000000,
    1920000000000], [5442000000000, 1920000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next
    ([1497000000000, 1920000000000], [5472000000000, 1920000000000]) (some (0, 8, 4)) (some (0, 8,
    4)) (.next ([75000000000], [300000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next
    ([756000000000, -3840000000000], [3447000000000, 1920000000000]) (some (0, 8, 4)) (some (0, 8,
    4)) (.next ([1122000000000, 1920000000000], [5547000000000, 1920000000000]) (some (0, 8, 4))
    (some (0, 8, 4)) (.next ([822000000000, 1920000000000], [5397000000000, 1920000000000]) (some
    (0, 8, 4)) (some (0, 8, 4)) (.next ([228000000000, -1920000000000], [6114000000000,
    3840000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([153000000000, -1920000000000],
    [6144000000000, 3840000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([0, 0],
    [2016000000000, 5760000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([-222000000000,
    -1920000000000], [6219000000000, 3840000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next
    ([-45000000000], [795000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([-444000000000,
    -3840000000000], [5442000000000, 1920000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next
    ([-522000000000, -1920000000000], [6069000000000, 3840000000000]) (some (0, 8, 4)) (some (0, 8,
    4)) (.next ([-519000000000, -3840000000000], [5472000000000, 1920000000000]) (some (0, 8, 4))
    (some (0, 8, 4)) fan14Owner0Part0))))))))))))))))))))))))

theorem excluded8_0 : ExcludedOn (model8.B 0 ++ [step8.q]) 9000000000000 (model8.caps 0) (model8.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_1 : ExcludedOn (model8.B 1 ++ [step8.q]) 9000000000000 (model8.caps 1) (model8.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_2 : ExcludedOn (model8.B 2 ++ [step8.q]) 9000000000000 (model8.caps 2) (model8.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_3 : ExcludedOn (model8.B 3 ++ [step8.q]) 9000000000000 (model8.caps 3) (model8.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_5 : ExcludedOn (model8.B 5 ++ [step8.q]) 9000000000000 (model8.caps 5) (model8.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5475000000000], [570000000000]) (some (3, 0, 2))
      (some (3, 1, 2)) (.next ([5475000000000, 0], [3150000000000, 9000000000000]) (some (3, 1, 2))
      (some (4, 1, 2)) (.next ([3150000000000, 9000000000000], [2895000000000, -9000000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3150000000000, 9000000000000], [3150000000000,
      9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2895000000000, -9000000000000],
      [3150000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0, 0],
      [3150000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 3)) (.next ([-570000000000],
      [6045000000000]) (some (4, 1, 3)) (some (4, 2, 3)) (.next ([-3150000000000, -9000000000000],
      [8625000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-2895000000000,
      9000000000000], [6045000000000, 0]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-3150000000000,
      -9000000000000], [6300000000000, 18000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-3150000000000, -9000000000000], [6045000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.terminal (some (4, 2, 3)) (some (0, 2, 3)) (some (4, 2, 3))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_6 : ExcludedOn (model8.B 6 ++ [step8.q]) 9000000000000 (model8.caps 6) (model8.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded8_0
    · exact excluded8_1
    · exact excluded8_2
    · exact excluded8_3
    · exact (hj rfl).elim
    · exact excluded8_5
    · exact excluded8_6
    · exact excluded8_7
    · exact excluded8_8
    · exact excluded8_9
theorem next8 : model8.insert step8 = model9 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded9_0 : ExcludedOn (model9.B 0 ++ [step9.q]) 9000000000000 (model9.caps 0) (model9.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5997000000000, 1920000000000], [222000000000,
      1920000000000]) (some (6, 8, 3)) (some (6, 8, 3)) (.next ([750000000000], [45000000000]) (some
      (6, 8, 3)) (some (6, 8, 3)) (.next ([4998000000000, -1920000000000], [444000000000,
      3840000000000]) (some (6, 8, 3)) (some (6, 8, 3)) (.next ([5547000000000, 1920000000000],
      [522000000000, 1920000000000]) (some (6, 8, 3)) (some (6, 8, 4)) (.next ([4953000000000,
      -1920000000000], [519000000000, 3840000000000]) (some (6, 8, 4)) (some (6, 8, 4)) (.next
      ([4653000000000, -1920000000000], [894000000000, 3840000000000]) (some (6, 8, 4)) (some (6, 8,
      4)) (.next ([4203000000000, -1920000000000], [1194000000000, 3840000000000]) (some (6, 8, 4))
      (some (6, 8, 4)) (.next ([2931000000000, -3840000000000], [897000000000, 1920000000000]) (some
      (6, 8, 4)) (some (6, 8, 4)) (.next ([300000000000], [150000000000]) (some (6, 8, 4)) (some (6,
      8, 4)) (.next ([5175000000000], [4995000000000]) (some (6, 8, 4)) (some (7, 8, 4)) (.next
      ([5100000000000], [5025000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([672000000000,
      1920000000000], [672000000000, 1920000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next
      ([4725000000000], [5100000000000]) (some (7, 8, 4)) (some (7, 8, 4))
      fan9Owner0Part1)))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_1 : ExcludedOn (model9.B 1 ++ [step9.q]) 9000000000000 (model9.caps 1) (model9.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_2 : ExcludedOn (model9.B 2 ++ [step9.q]) 9000000000000 (model9.caps 2) (model9.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_3 : ExcludedOn (model9.B 3 ++ [step9.q]) 9000000000000 (model9.caps 3) (model9.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_5 : ExcludedOn (model9.B 5 ++ [step9.q]) 9000000000000 (model9.caps 5) (model9.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4500000000000, 0], [1125000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([2730000000000], [1545000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3150000000000, 9000000000000], [2895000000000,
      -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([4500000000000], [4275000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3150000000000, 9000000000000], [3150000000000,
      9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2895000000000, -9000000000000],
      [3150000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1350000000000,
      -9000000000000], [7425000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 3)) (.next ([0,
      0], [3150000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-1125000000000,
      9000000000000], [5625000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 2, 3)) (.next
      ([-1545000000000], [4275000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2895000000000,
      9000000000000], [6045000000000, 0]) (some (0, 2, 3)) (some (0, 2, 4)) (.next
      ([-4275000000000], [8775000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-3150000000000,
      -9000000000000], [6300000000000, 18000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-3150000000000, -9000000000000], [6045000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-7425000000000, -9000000000000], [8775000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_6 : ExcludedOn (model9.B 6 ++ [step9.q]) 9000000000000 (model9.caps 6) (model9.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_7 : ExcludedOn (model9.B 7 ++ [step9.q]) 9000000000000 (model9.caps 7) (model9.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded9_0
    · exact excluded9_1
    · exact excluded9_2
    · exact excluded9_3
    · exact (hj rfl).elim
    · exact excluded9_5
    · exact excluded9_6
    · exact excluded9_7
    · exact excluded9_8
    · exact excluded9_9
theorem next9 : model9.insert step9 = model10 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded10_0 : ExcludedOn (model10.B 0 ++ [step10.q]) 9000000000000 (model10.caps 0)
    (model10.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_1 : ExcludedOn (model10.B 1 ++ [step10.q]) 9000000000000 (model10.caps 1)
    (model10.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_2 : ExcludedOn (model10.B 2 ++ [step10.q]) 9000000000000 (model10.caps 2)
    (model10.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_3 : ExcludedOn (model10.B 3 ++ [step10.q]) 9000000000000 (model10.caps 3)
    (model10.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_5 : ExcludedOn (model10.B 5 ++ [step10.q]) 9000000000000 (model10.caps 5)
    (model10.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3795000000000], [375000000000]) (some (3, 0, 2))
      (some (3, 1, 2)) (.next ([5670000000000, 0], [1275000000000, 9000000000000]) (some (3, 1, 2))
      (some (4, 1, 2)) (.next ([1875000000000, 0], [645000000000, -9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([3150000000000, 9000000000000], [2895000000000, -9000000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3150000000000, 9000000000000], [3150000000000,
      9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2895000000000, -9000000000000],
      [3150000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1875000000000],
      [3795000000000]) (some (4, 1, 2)) (some (4, 1, 3)) (.next ([0, 0], [3150000000000,
      9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-375000000000], [4170000000000])
      (some (4, 1, 3)) (some (4, 2, 3)) (.next ([-1275000000000, -9000000000000], [6945000000000,
      9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-645000000000, 9000000000000],
      [2520000000000, -9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-2895000000000,
      9000000000000], [6045000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3150000000000,
      -9000000000000], [6300000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-3150000000000, -9000000000000], [6045000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-3795000000000], [5670000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded10_6 : ExcludedOn (model10.B 6 ++ [step10.q]) 9000000000000 (model10.caps 6)
    (model10.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded10_0
    · exact excluded10_1
    · exact excluded10_2
    · exact excluded10_3
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 4 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_5 : ExcludedOn (model11.B 5 ++ [step11.q]) 9000000000000 (model11.caps 5)
    (model11.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3150000000000, 9000000000000], [2895000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([3225000000000], [3150000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3150000000000, 9000000000000], [3150000000000,
      9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2895000000000, -9000000000000],
      [3150000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([330000000000],
      [2820000000000]) (some (4, 1, 2)) (some (4, 1, 3)) (.next ([0, 9000000000000], [3225000000000,
      -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0, 0], [3150000000000,
      9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2895000000000, 9000000000000],
      [6045000000000, 0]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-3150000000000],
      [6375000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3150000000000, -9000000000000],
      [6300000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3150000000000,
      -9000000000000], [6045000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2820000000000],
      [3150000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3225000000000, 9000000000000],
      [3225000000000, 0]) (some (0, 2, 3)) (some (0, 2, 4)) (.terminal (some (0, 2, 4)) (some (0, 2,
      4)) (some (0, 2, 4))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100 (by decide +kernel)
  decide +kernel

theorem excluded11_6 : ExcludedOn (model11.B 6 ++ [step11.q]) 9000000000000 (model11.caps 6)
    (model11.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_7 : ExcludedOn (model11.B 7 ++ [step11.q]) 9000000000000 (model11.caps 7)
    (model11.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_8 : ExcludedOn (model11.B 8 ++ [step11.q]) 9000000000000 (model11.caps 8)
    (model11.ord 8) 0 1 100 := by
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
    · exact (hj rfl).elim
    · exact excluded11_5
    · exact excluded11_6
    · exact excluded11_7
    · exact excluded11_8
    · exact excluded11_9
theorem next11 : model11.insert step11 = model12 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded12_0 : ExcludedOn (model12.B 0 ++ [step12.q]) 9000000000000 (model12.caps 0)
    (model12.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_5 : ExcludedOn (model12.B 5 ++ [step12.q]) 9000000000000 (model12.caps 5)
    (model12.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000], [2775000000000]) (some (4, 0,
      2)) (some (4, 1, 2)) (.next ([3150000000000, 9000000000000], [2895000000000, -9000000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3150000000000, 9000000000000], [3150000000000,
      9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2895000000000, -9000000000000],
      [3150000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([855000000000],
      [1920000000000]) (some (4, 1, 2)) (some (4, 1, 3)) (.next ([975000000000, -9000000000000],
      [5925000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([375000000000,
      9000000000000], [3750000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0,
      0], [3150000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-2775000000000], [6900000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-2895000000000,
      9000000000000], [6045000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3150000000000,
      -9000000000000], [6300000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-3150000000000, -9000000000000], [6045000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-1920000000000], [2775000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-5925000000000,
      -9000000000000], [6900000000000]) (some (0, 2, 3)) (some (0, 2, 4)) (.next ([-3750000000000,
      9000000000000], [4125000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded12_6 : ExcludedOn (model12.B 6 ++ [step12.q]) 9000000000000 (model12.caps 6)
    (model12.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5997000000000, 1920000000000], [222000000000,
      1920000000000]) (some (6, 8, 3)) (some (6, 8, 3)) (.next ([750000000000], [45000000000]) (some
      (6, 8, 3)) (some (6, 8, 3)) (.next ([4998000000000, -1920000000000], [444000000000,
      3840000000000]) (some (6, 8, 3)) (some (6, 8, 3)) (.next ([5547000000000, 1920000000000],
      [522000000000, 1920000000000]) (some (6, 8, 3)) (some (6, 8, 4)) (.next ([4953000000000,
      -1920000000000], [519000000000, 3840000000000]) (some (6, 8, 4)) (some (6, 8, 4))
      fan13Owner0Part1)))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_5 : ExcludedOn (model13.B 5 ++ [step13.q]) 9000000000000 (model13.caps 5)
    (model13.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4500000000000], [2700000000000]) (some (4, 0,
      2)) (some (4, 1, 2)) (.next ([3150000000000, 9000000000000], [2895000000000, -9000000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3150000000000, 9000000000000], [3150000000000,
      9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2895000000000, -9000000000000],
      [3150000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1155000000000],
      [1545000000000]) (some (4, 1, 2)) (some (4, 1, 3)) (.next ([1350000000000, -9000000000000],
      [5850000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([450000000000,
      9000000000000], [4050000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0,
      0], [3150000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-2700000000000], [7200000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-2895000000000,
      9000000000000], [6045000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3150000000000,
      -9000000000000], [6300000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-3150000000000, -9000000000000], [6045000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-1545000000000], [2700000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-5850000000000,
      -9000000000000], [7200000000000]) (some (0, 2, 3)) (some (0, 2, 4)) (.next ([-4050000000000,
      9000000000000], [4500000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_6 : ExcludedOn (model13.B 6 ++ [step13.q]) 9000000000000 (model13.caps 6)
    (model13.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5997000000000, 1920000000000], [222000000000,
      1920000000000]) (some (6, 8, 8)) (some (6, 8, 8)) (.next ([750000000000], [45000000000]) (some
      (6, 8, 8)) (some (6, 8, 8)) (.next ([4998000000000, -1920000000000], [444000000000,
      3840000000000]) (some (6, 8, 8)) (some (6, 8, 8)) (.next ([5547000000000, 1920000000000],
      [522000000000, 1920000000000]) (some (6, 8, 8)) (some (6, 8, 8)) (.next ([4953000000000,
      -1920000000000], [519000000000, 3840000000000]) (some (6, 8, 8)) (some (6, 8, 8)) (.next
      ([4653000000000, -1920000000000], [894000000000, 3840000000000]) (some (6, 8, 8)) (some (6, 8,
      8)) (.next ([7770000000000], [1875000000000]) (some (6, 8, 8)) (some (6, 8, 8)) (.next
      ([7725000000000], [1950000000000]) (some (6, 8, 4)) (some (6, 8, 4)) (.next ([4203000000000,
      -1920000000000], [1194000000000, 3840000000000]) (some (6, 8, 4)) (some (6, 8, 4)) (.next
      ([7425000000000], [2325000000000]) (some (6, 8, 4)) (some (6, 8, 4)) (.next ([6975000000000],
      [2625000000000]) (some (6, 8, 4)) (some (6, 8, 4)) fan14Owner0Part1)))))))))))) (den :=
      9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded14_1 : ExcludedOn (model14.B 1 ++ [step14.q]) 9000000000000 (model14.caps 1)
    (model14.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_2 : ExcludedOn (model14.B 2 ++ [step14.q]) 9000000000000 (model14.caps 2)
    (model14.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_3 : ExcludedOn (model14.B 3 ++ [step14.q]) 9000000000000 (model14.caps 3)
    (model14.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_4 : ExcludedOn (model14.B 4 ++ [step14.q]) 9000000000000 (model14.caps 4)
    (model14.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_5 : ExcludedOn (model14.B 5 ++ [step14.q]) 9000000000000 (model14.caps 5)
    (model14.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3750000000000, -9000000000000], [375000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([5925000000000, 9000000000000],
      [975000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 4)) (.next ([1920000000000],
      [855000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([3150000000000, 9000000000000],
      [2895000000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([3150000000000,
      9000000000000], [3150000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([2895000000000, -9000000000000], [3150000000000, 9000000000000]) (some (0, 1, 4)) (some (0,
      1, 4)) (.next ([2775000000000], [4125000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0,
      0], [3150000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-375000000000,
      -9000000000000], [4125000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-975000000000,
      9000000000000], [6900000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-855000000000],
      [2775000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2895000000000, 9000000000000],
      [6045000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3150000000000,
      -9000000000000], [6300000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-3150000000000, -9000000000000], [6045000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-4125000000000], [6900000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded14_3
    · exact excluded14_4
    · exact excluded14_5
    · exact (hj rfl).elim
    · exact excluded14_7
    · exact excluded14_8
    · exact excluded14_9
theorem next14 : model14.insert step14 = model15 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded15_0 : ExcludedOn (model15.B 0 ++ [step15.q]) 9000000000000 (model15.caps 0)
    (model15.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_4 : ExcludedOn (model15.B 4 ++ [step15.q]) 9000000000000 (model15.caps 4)
    (model15.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_5 : ExcludedOn (model15.B 5 ++ [step15.q]) 9000000000000 (model15.caps 5)
    (model15.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6045000000000], [3150000000000]) (some (3, 0,
      2)) (some (3, 4, 2)) (.next ([3150000000000, 9000000000000], [2895000000000, -9000000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([3150000000000, 9000000000000], [3150000000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([2895000000000, -9000000000000],
      [3150000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 9000000000000],
      [3150000000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next ([0, 0], [3150000000000,
      9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3150000000000], [9195000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-2895000000000, 9000000000000], [6045000000000, 0])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3150000000000, -9000000000000], [6300000000000,
      18000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3150000000000, -9000000000000],
      [6045000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3150000000000, 0],
      [3150000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 2, 3))
      (some (0, 2, 3)) (some (0, 2, 3))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded15_6 : ExcludedOn (model15.B 6 ++ [step15.q]) 9000000000000 (model15.caps 6)
    (model15.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded15_5
    · exact excluded15_6
    · exact excluded15_7
    · exact excluded15_8
    · exact (hj rfl).elim
theorem next15 : model15.insert step15 = model16 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint350000360000
end ConwaySoifer.Simplified.Certificates
