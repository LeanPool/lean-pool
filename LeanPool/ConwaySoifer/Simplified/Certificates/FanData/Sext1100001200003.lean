/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Certificates.Witness

/-! Exact fan data for Sext1100001200003. -/

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
namespace Sext110000120000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner3Part0 : FanWitness := (.next ([1890000000000, 9000000000000], [3150000000000,
    -9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([1830000000000], [3705000000000])
    (some (6, 1, 3)) (some (6, 1, 4)) (.next ([990000000000, 9000000000000], [2055000000000,
    -9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([990000000000], [4260000000000])
    (some (6, 1, 4)) (some (6, 1, 4)) (.next ([900000000000], [4140000000000]) (some (6, 1, 4))
    (some (6, 1, 4)) (.next ([330000000000, 9000000000000], [5535000000000]) (some (6, 1, 4)) (some
    (6, 1, 4)) (.next ([0], [990000000000, 9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
    ([0, -9000000000000], [4260000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-90000000000,
    -9000000000000], [4140000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-285000000000],
    [3885000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-660000000000], [5535000000000])
    (some (6, 1, 4)) (some (6, 2, 4)) (.next ([-495000000000], [3975000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([-660000000000], [4545000000000, -9000000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([-2055000000000], [7305000000000]) (some (6, 2, 4)) (some (6, 2, 4))
    (.next ([-2145000000000], [7185000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-990000000000, -9000000000000], [1980000000000, 18000000000000]) (some (6, 2, 4)) (some (6, 2,
    4)) (.next ([-120000000000], [210000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-3270000000000, 9000000000000], [5250000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-3150000000000, 9000000000000], [5040000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-3705000000000], [5535000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-2055000000000,
    9000000000000], [3045000000000]) (some (1, 2, 4)) (some (1, 2, 4)) (.next ([-4260000000000],
    [5250000000000]) (some (1, 2, 4)) (some (1, 2, 4)) (.next ([-4140000000000], [5040000000000])
    (some (1, 2, 4)) (some (1, 2, 4)) (.next ([-5535000000000, 0], [5865000000000, 9000000000000])
    (some (1, 2, 4)) (some (1, 2, 4)) (.terminal (some (1, 2, 4)) (some (1, 2, 4)) (some (1, 2,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner3Part1 : FanWitness := (.next ([1890000000000, 9000000000000], [3150000000000,
    -9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([990000000000, 9000000000000],
    [2055000000000, -9000000000000]) (some (6, 1, 3)) (some (6, 1, 4)) (.next ([1830000000000],
    [3705000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([990000000000], [4260000000000])
    (some (6, 1, 4)) (some (6, 1, 4)) (.next ([900000000000], [4140000000000]) (some (6, 1, 4))
    (some (6, 1, 4)) (.next ([330000000000, 9000000000000], [5535000000000]) (some (6, 1, 4)) (some
    (6, 1, 4)) (.next ([0], [990000000000, 9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
    ([0, -9000000000000], [4260000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-90000000000,
    -9000000000000], [4140000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-285000000000],
    [3885000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-660000000000], [5535000000000])
    (some (6, 1, 4)) (some (6, 2, 4)) (.next ([-495000000000], [3975000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([-660000000000], [4545000000000, -9000000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([-2055000000000], [7305000000000]) (some (6, 2, 4)) (some (6, 2, 4))
    (.next ([-2145000000000], [7185000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-990000000000, -9000000000000], [1980000000000, 18000000000000]) (some (6, 2, 4)) (some (6, 2,
    4)) (.next ([-120000000000], [210000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-3270000000000, 9000000000000], [5250000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-3150000000000, 9000000000000], [5040000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-2055000000000, 9000000000000], [3045000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-3705000000000], [5535000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-4260000000000],
    [5250000000000]) (some (1, 2, 4)) (some (1, 2, 4)) (.next ([-4140000000000], [5040000000000])
    (some (1, 2, 4)) (some (1, 2, 4)) (.next ([-5535000000000, 0], [5865000000000, 9000000000000])
    (some (1, 2, 4)) (some (1, 2, 4)) (.terminal (some (1, 2, 4)) (some (1, 2, 4)) (some (1, 2,
    4)))))))))))))))))))))))))))

end Sext110000120000
end ConwaySoifer.Simplified.Certificates
