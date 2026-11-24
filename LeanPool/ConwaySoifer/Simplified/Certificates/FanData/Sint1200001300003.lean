/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Certificates.Witness

/-! Exact fan data for Sint1200001300003. -/

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

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sint120000130000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner0Part0 : FanWitness := (.next ([6870000000000], [3210000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([313200000000, 2610000000000], [313200000000, 2610000000000]) (some (0,
    2, 6)) (some (0, 2, 6)) (.next ([1603200000000, 2610000000000], [8023200000000, 2610000000000])
    (some (0, 2, 6)) (some (0, 3, 6)) (.next ([976800000000, -2610000000000], [7396800000000,
    -2610000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([976800000000, -2610000000000],
    [8336400000000, 5220000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([663600000000,
    -5220000000000], [8023200000000, 2610000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([251400000000, 5220000000000], [5446800000000, -2610000000000]) (some (0, 3, 6)) (some (0, 6,
    6)) (.next ([0, 0], [939600000000, 7830000000000]) (some (0, 6, 6)) (some (0, 6, 6)) (.next
    ([-61800000000, 2610000000000], [6073200000000, 2610000000000]) (some (0, 6, 6)) (some (0, 6,
    6)) (.next ([-453600000000, 5220000000000], [5266800000000, -2610000000000]) (some (0, 6, 6))
    (some (0, 6, 6)) (.next ([-688200000000, -2610000000000], [6386400000000, 5220000000000]) (some
    (0, 6, 6)) (some (1, 6, 6)) (.next ([-766800000000, 2610000000000], [5893200000000,
    2610000000000]) (some (1, 6, 6)) (some (1, 6, 6)) (.next ([-1001400000000, -5220000000000],
    [6073200000000, 2610000000000]) (some (1, 6, 6)) (some (1, 6, 6)) (.next ([-180000000000],
    [885000000000]) (some (1, 6, 6)) (some (1, 6, 6)) (.next ([-1393200000000, -2610000000000],
    [6206400000000, 5220000000000]) (some (1, 6, 6)) (some (1, 6, 6)) (.next ([-2325000000000],
    [9375000000000]) (some (1, 6, 6)) (some (1, 6, 6)) (.next ([-1706400000000, -5220000000000],
    [5893200000000, 2610000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-3210000000000],
    [10080000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-313200000000, -2610000000000],
    [626400000000, 5220000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-8023200000000,
    -2610000000000], [9626400000000, 5220000000000]) (some (1, 6, 5)) (some (2, 6, 5)) (.next
    ([-7396800000000, 2610000000000], [8373600000000, -5220000000000]) (some (2, 6, 5)) (some (2, 6,
    5)) (.next ([-8336400000000, -5220000000000], [9313200000000, 2610000000000]) (some (2, 6, 5))
    (some (2, 6, 5)) (.next ([-8023200000000, -2610000000000], [8686800000000, -2610000000000])
    (some (2, 6, 5)) (some (2, 6, 5)) (.next ([-5446800000000, 2610000000000], [5698200000000,
    2610000000000]) (some (2, 6, 5)) (some (2, 6, 5)) (.terminal (some (2, 6, 5)) (some (2, 6, 5))
    (some (2, 6, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner5Part0 : FanWitness := (.next ([3825000000000], [855000000000]) (some (5, 1, 2)) (some
    (5, 1, 2)) (.next ([3825000000000], [1080000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([3240000000000], [1080000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3015000000000],
    [1080000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2745000000000, -9000000000000],
    [1935000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2745000000000,
    -9000000000000], [2160000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next
    ([2745000000000], [5175000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([660000000000],
    [2085000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1155000000000], [3825000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1665000000000, -9000000000000], [6255000000000,
    9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([930000000000], [3825000000000]) (some
    (0, 1, 3)) (some (0, 1, 3)) (.next ([0], [5835000000000]) (some (0, 1, 3)) (some (0, 1, 3))
    (.next ([-1080000000000, -9000000000000], [6915000000000, 9000000000000]) (some (0, 1, 3)) (some
    (0, 2, 4)) (.next ([-855000000000], [4680000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-1080000000000], [4905000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1080000000000],
    [4320000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1080000000000], [4095000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1935000000000, -9000000000000], [4680000000000])
    (some (0, 2, 4)) (some (0, 2, 5)) (.next ([-2160000000000, -9000000000000], [4905000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5175000000000], [7920000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-2085000000000], [2745000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-3825000000000], [4980000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-6255000000000, -9000000000000], [7920000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-3825000000000], [4755000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2,
    5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan31Owner6Part0 : FanWitness := (.next ([1875000000000], [540000000000]) (some (0, 5, 4)) (some
    (0, 5, 4)) (.next ([870000000000], [255000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([750000000000, 0], [330000000000, -9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([5760000000000], [3240000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([4680000000000,
    -9000000000000], [3240000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([5760000000000],
    [4320000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([1080000000000,
    9000000000000], [1080000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([3600000000000], [3990000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([3345000000000],
    [5115000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([750000000000], [1410000000000])
    (some (0, 5, 4)) (some (5, 5, 4)) (.next ([540000000000, 9000000000000], [1335000000000,
    -9000000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([0, 0], [1080000000000,
    9000000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-330000000000, -9000000000000],
    [2490000000000, 9000000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-540000000000],
    [2415000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-255000000000], [1125000000000])
    (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-330000000000, 9000000000000], [1080000000000,
    -9000000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-3240000000000], [9000000000000])
    (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-3240000000000, 0], [7920000000000, -9000000000000])
    (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-4320000000000, -9000000000000], [10080000000000,
    9000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-1080000000000, -9000000000000],
    [2160000000000, 18000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-3990000000000],
    [7590000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-5115000000000], [8460000000000])
    (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-1410000000000], [2160000000000]) (some (5, 3, 4))
    (some (5, 3, 4)) (.next ([-1335000000000, 9000000000000], [1875000000000]) (some (5, 3, 4))
    (some (5, 3, 4)) (.terminal (some (5, 3, 4)) (some (5, 3, 0)) (some (5, 3,
    4)))))))))))))))))))))))))))

end Sint120000130000
end ConwaySoifer.Simplified.Certificates
